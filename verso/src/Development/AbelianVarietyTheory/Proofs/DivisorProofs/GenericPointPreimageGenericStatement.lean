import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPreimageGeneric
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFiniteCompDegreeMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGenericPointPreimageGeneric.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.generic_point_preimage_generic : ∀ (T T' : Scheme.{0}) [IsIntegral T] [IsIntegral T'] (ρ : T' ⟶ T) (d : ℕ), IsGenFinite ρ d → ∀ x : T', ρ x = genericPoint T → x = genericPoint T' := by
  first | exact @GlobalTheory.GenFiniteFibre.eq_genericPoint_of_apply_eq | exact GlobalTheory.GenFiniteFibre.eq_genericPoint_of_apply_eq | (intros; apply GlobalTheory.GenFiniteFibre.eq_genericPoint_of_apply_eq <;> assumption)
