import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsRatOfForallComplexRingEquivFixed.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed : ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  first | exact @GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | exact GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed <;> assumption)
