import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AevalSumElimEqZeroOfMemPts
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FAevalSumElimEqZeroOfMemPts.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.aeval_sum_elim_eq_zero_of_mem_pts' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  first | exact @GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | exact GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | (intros; apply GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts <;> assumption)
