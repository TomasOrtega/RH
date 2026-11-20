import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftInvariantPolySeparatingCoset
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.exists_isInv_evC_one_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsLeftInvariantPolySeparatingCoset.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.exists_leftInvariantPoly_separating_coset : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  first | exact @GlobalTheory.ClassFin.exists_isInv_evC_one_ne | exact GlobalTheory.ClassFin.exists_isInv_evC_one_ne | (intros; apply GlobalTheory.ClassFin.exists_isInv_evC_one_ne <;> assumption)
