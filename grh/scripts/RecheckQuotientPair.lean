import New.Determinant.Chain.Moduli
import Lean.Elab.Command

/-!
# Focused kernel check for the determinant quotient pair

From `grh/`, run `lake lean scripts/RecheckQuotientPair.lean` after building the
readable edition. The check replays the public definition `New.Data.quotientPair`
and its named private theorems. It reports each rejected declaration or, on
success, the number of private theorems it checked.
The ordinary import environment supplies their dependencies. Omitting the
`module` header is intentional so the kernel can see the imported definitions.

The check specializes the per-declaration replay used to diagnose
[upstream issue #7560](https://github.com/leanprover-community/riemann-hypothesis/issues/7560#issuecomment-7198168985).
The whole-proof comparator separately exports the headline theorems and
checks their dependency closure in a fresh environment.
-/

open Lean Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  let mainDecl := `New.Data.quotientPair
  let some (.defnInfo parent) := env.find? mainDecl
    | throwError "missing definition {mainDecl}"
  let maxHb := (Core.getMaxHeartbeats (← getOptions)).toUSize
  let depth := defaultMaxRecDepth.toUSize
  let mut checked : Nat := 0
  let mut rejected : Array MessageData := #[]
  let mut sawModule := false
  for i in [0:env.header.moduleData.size] do
    if env.header.moduleNames[i]! == `New.Determinant.Chain.Moduli then
      sawModule := true
      for n in env.header.moduleData[i]!.constNames do
        unless isPrivateName n && mainDecl.isPrefixOf (privateToUserName n) do continue
        let some (.thmInfo thm) := env.find? n | continue
        let probe := Declaration.thmDecl { thm with name := `RecheckProbe ++ n }
        checked := checked + 1
        if let .error err := env.addDeclCore maxHb depth probe none then
          rejected := rejected.push m!"kernel rejected {n}\n{err.toMessageData {}}"
  unless sawModule do
    throwError "missing determinant module for {mainDecl}"
  let newName := `RecheckProbe ++ mainDecl
  let probe := Declaration.defnDecl { parent with name := newName, all := [newName] }
  if let .error err := env.addDeclCore maxHb depth probe none then
    rejected := rejected.push m!"kernel rejected {mainDecl}\n{err.toMessageData {}}"
  unless rejected.isEmpty do
    throwError "{MessageData.joinSep rejected.toList Format.line}"
  logInfo m!"kernel accepted {mainDecl} and {checked} associated private theorem declarations"
