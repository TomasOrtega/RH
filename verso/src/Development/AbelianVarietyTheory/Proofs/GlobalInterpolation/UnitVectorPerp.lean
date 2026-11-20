import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerpAllIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis

namespace GlobalTheory.UnitPerpObj

/- English proof (translation)
The claim follows from `(GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)`.
-/
theorem unitVectorPerp (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements.UnitVectorPerp D :=
  (GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)

end GlobalTheory.UnitPerpObj
