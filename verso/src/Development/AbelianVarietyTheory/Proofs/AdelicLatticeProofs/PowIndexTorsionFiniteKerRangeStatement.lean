import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionFiniteKerRange
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FPowIndexTorsionFiniteKerRange.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.powIndex_torsion_finite_ker_range : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 → pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  first | exact @GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | exact GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | (intros; apply GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero <;> assumption)
