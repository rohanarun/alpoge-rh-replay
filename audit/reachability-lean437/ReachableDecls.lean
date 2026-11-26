/-
Task-local measurement helper. This does not check proofs.
Dependency rules mirror LeanExport.Basic at Lean commit
0b77e12952ad39077d80d8bd6b66d601f225c321 (format 3.1.0).
-/
import Lean

open Lean

namespace ReachableDecls

def pinnedCommit := "0b77e12952ad39077d80d8bd6b66d601f225c321"

structure Context where
  env : Environment
  recursors : NameMap NameSet
  exportUnsafe : Bool

structure State where
  pending : List Name := []
  requested : NameHashSet := {}
  reachable : NameHashSet := {}
  skippedUnsafe : NameHashSet := {}

abbrev M := ReaderT Context (StateT State IO)

def fail (message : String) : M α :=
  throw <| IO.userError message

def lookup (name : Name) : M ConstantInfo := do
  match (← read).env.find? name with
  | some info => return info
  | none => fail s!"missing declaration: {name}"

def enqueue (name : Name) : M Unit := do
  unless (← get).requested.contains name || (← get).reachable.contains name do
    modify fun s => { s with
      requested := s.requested.insert name
      pending := name :: s.pending }

def record (info : ConstantInfo) : M Unit :=
  modify fun s => { s with reachable := s.reachable.insert info.name }

def requireSafeMember (info : ConstantInfo) : M Unit := do
  if info.isUnsafe && !(← read).exportUnsafe then
    fail s!"unsafe member of a reached inductive block: {info.name}"

/-- One temporary expression cache per call; no global expression-node table. -/
def scanExpr (expr : Expr) (constants := true) : M Unit := do
  expr.forEach fun e => do
    match e with
    | .const name _ => if constants then enqueue name else pure ()
    | .proj name _ _ => if constants then enqueue name else pure ()
    | .lit (.natVal _) => do
      if ((← read).env.find? ``Nat).isSome then enqueue ``Nat
    | .lit (.strVal _) => do
      for name in [``Char.ofNat, ``String.ofList] do
        if ((← read).env.find? name).isSome then enqueue name
    | .fvar .. | .mvar .. => fail "free variable or metavariable in a stored declaration"
    | _ => pure ()

/-- Expand exactly the inductive/constructor/recursor unit emitted by the exporter. -/
def scanInductive (base : InductiveVal) : M Unit := do
  let mut ctors : Array ConstructorVal := #[]
  let mut recNames : NameSet := {}
  for name in base.all do
    let info ← lookup name
    let .inductInfo val := info
      | fail s!"expected inductive declaration: {name}"
    requireSafeMember info
    record info
    scanExpr val.type
    for ctor in val.ctors do
      let info ← lookup ctor
      let .ctorInfo val := info
        | fail s!"expected constructor declaration: {ctor}"
      requireSafeMember info
      ctors := ctors.push val
    -- Deliberately use base.name, as LeanExport.Basic does.
    if let some names := (← read).recursors.get? base.name then
      recNames := recNames.union names
    else if !ctors.isEmpty then
      fail s!"missing recursor metadata for inductive block: {base.name}"
  for ctor in ctors do
    record (.ctorInfo ctor)
    scanExpr ctor.type
  let mut recs : Array RecursorVal := #[]
  for name in recNames do
    let info ← lookup name
    let .recInfo val := info
      | fail s!"expected recursor declaration: {name}"
    requireSafeMember info
    record info
    recs := recs.push val
    scanExpr val.type
  for rec in recs do
    for rule in rec.rules do
      scanExpr rule.rhs

def visit (name : Name) : M Unit := do
  if (← get).reachable.contains name then return
  let info ← lookup name
  if info.isUnsafe && !(← read).exportUnsafe then
    modify fun s => { s with skippedUnsafe := s.skippedUnsafe.insert name }
    return
  record info
  match info with
  | .axiomInfo val => scanExpr val.type
  | .defnInfo val => do scanExpr val.type; scanExpr val.value
  | .opaqueInfo val => do scanExpr val.type; scanExpr val.value
  | .thmInfo val => do scanExpr val.type; scanExpr val.value
  | .inductInfo val => scanInductive val
  | .ctorInfo val => enqueue val.induct
  | .recInfo val => do for name in val.all do enqueue name
  | .quotInfo _ => do
    enqueue ``Eq
    for name in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let info ← lookup name
      let .quotInfo val := info
        | fail s!"expected quotient declaration: {name}"
      record info
      -- The exporter serializes these types but does not call dumpDeps on them.
      -- Serialization adds literal dependencies only.
      scanExpr val.type (constants := false)

partial def drain : M Unit := do
  match (← get).pending with
  | [] => pure ()
  | name :: rest => do
    modify fun s => { s with pending := rest }
    visit name
    drain

def recursorMap (env : Environment) : NameMap NameSet := Id.run do
  let mut result : NameMap NameSet := {}
  for (_, info) in env.constants do
    if let .recInfo val := info then
      for name in val.all do
        result := result.alter name fun
          | none => some <| NameSet.empty.insert val.name
          | some names => some <| names.insert val.name
  return result

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def kinds : Array String :=
  #["axiom", "definition", "opaque", "theorem", "quotient", "inductive", "constructor", "recursor"]

/-- Components retain exact identity even for escaped or numeric name components. -/
def nameParts : Name → List Json
  | .anonymous => []
  | .str parent value => nameParts parent ++ [toJson value]
  | .num parent value => nameParts parent ++ [toJson value]

def sortedNames (names : NameHashSet) : Array (Name × String) := Id.run do
  let result := (Std.HashSet.toArray (α := Name) names).map fun name => (name, name.toString)
  return result.qsort fun a b =>
    let order := compare a.2 b.2
    if order == .eq then a.1.cmp b.1 == .lt else order == .lt

def decodeName (text : String) : IO Name := do
  match Syntax.decodeNameLit ("`" ++ text) with
  | some name => do
    if name.isAnonymous then throw <| IO.userError "anonymous name is not a target"
    return name
  | none => throw <| IO.userError s!"invalid Lean name: {text}"

/-- Match the whitespace-separated frozen export-targets.txt interface. No comments/options. -/
def words (text : String) : List String := Id.run do
  let mut result := []
  let mut current := ""
  for char in text.toList do
    if char.isWhitespace then
      unless current.isEmpty do result := current :: result
      current := ""
    else current := current.push char
  unless current.isEmpty do result := current :: result
  return result.reverse

def run (moduleText targetsPath namesPath : String) (exportUnsafe : Bool) : IO Unit := do
  if Lean.githash != pinnedCommit then
    throw <| IO.userError s!"wrong Lean commit: expected {pinnedCommit}, got {Lean.githash}"
  if ← System.FilePath.pathExists namesPath then
    throw <| IO.userError s!"refusing to overwrite names output: {namesPath}"
  let moduleName ← decodeName moduleText
  let targetsText ← IO.FS.readFile targetsPath
  let targets ← (words targetsText).mapM decodeName
  if targets.isEmpty then throw <| IO.userError "targets file is empty"
  initSearchPath (← findSysroot)
  -- Match leanexport: full private data, no extension initialization.
  let env ← importModules #[{ module := moduleName }] {}
    (loadExts := false) (level := .private)
  let context : Context := { env, recursors := recursorMap env, exportUnsafe }
  let action : M Unit := do
    for name in targets do enqueue name
    drain
  let (_, state) ← (action.run context).run {}
  let names := sortedNames state.reachable
  let counts ← IO.FS.withFile namesPath .write fun handle => do
    let mut counts : Std.HashMap String Nat := {}
    for (name, display) in names do
      let some info := env.find? name
        | throw <| IO.userError s!"reached declaration disappeared: {name}"
      let tag := kind info
      counts := counts.insert tag (counts.getD tag 0 + 1)
      handle.putStrLn <| (Json.mkObj [
        ("name", toJson display), ("components", toJson (nameParts name)), ("kind", toJson tag)
      ]).compress
    handle.flush
    return counts
  let report := Json.mkObj [
    ("schema", toJson "rh-reachable-declarations/1"),
    ("metric", toJson "stock-leanexport reachable declaration closure"),
    ("independentProofValidation", toJson false),
    ("expressionNodeCount", Json.null),
    ("leanVersion", toJson Lean.versionString),
    ("leanCommit", toJson Lean.githash),
    ("module", toJson moduleName.toString),
    ("targetsText", toJson targetsText),
    ("targets", toJson (targets.map fun name => name.toString)),
    ("exportUnsafe", toJson exportUnsafe),
    ("reachableDeclarationCount", toJson names.size),
    ("declarationCounts", Json.mkObj <| kinds.toList.map fun tag => (tag, toJson (counts.getD tag 0))),
    ("skippedUnsafe", toJson <| (sortedNames state.skippedUnsafe).map (·.2)),
    ("namesFormat", toJson "NDJSON records sorted by displayed Lean name; components preserve identity")
  ]
  IO.println report.compress

end ReachableDecls

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [mod, targets, names] => ReachableDecls.run mod targets names false
    | [mod, targets, names, "--export-unsafe"] => ReachableDecls.run mod targets names true
    | _ => throw <| IO.userError "usage: ReachableDecls.lean MODULE TARGETS_FILE NEW_NAMES_JSONL [--export-unsafe]"
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"reachability failed: {error}"
    return 1
