/- These are small exporter/traversal fixtures, not a proof contribution. -/
module
public import Lean

namespace ReachabilityFixtures

private theorem hiddenProof : True := True.intro
public theorem viaPrivate : True := hiddenProof

private def hiddenNat : Nat := 17
public opaque opaqueNat : Nat := hiddenNat
public def viaOpaque : Nat := opaqueNat

public def TypeMarker : Prop := True
public theorem typeOnly : TypeMarker := True.intro

mutual
  public inductive Left where
    | leaf : Nat → Left
    | next : Right → Left
  public inductive Right where
    | leaf : String → Right
    | next : Left → Right
end

public inductive Nested where
  | node : List Nested → Nested

public structure Bundle where
  proof : True
  value : Nat

public def projectValue (bundle : Bundle) : Nat := bundle.value
public def natLiteral : Nat := 123456789
public def stringLiteral : String := "reachability λ"

public def metadataOnlyMention : Nat := 99

open Lean Elab Term in
elab "fixtureMetadataProof" : term =>
  pure <| mkMData (KVMap.empty.insert `fixtureMetadata (.ofName `ReachabilityFixtures.metadataOnlyMention))
    (mkConst ``True.intro)

public theorem metadataRoot : True := fixtureMetadataProof

end ReachabilityFixtures
