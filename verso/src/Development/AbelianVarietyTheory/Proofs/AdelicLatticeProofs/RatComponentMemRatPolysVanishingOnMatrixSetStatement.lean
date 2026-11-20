import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatComponentMemRatPolysVanishingOnMatrixSet
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FRatComponentMemRatPolysVanishingOnMatrixSet.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.rat_component_mem_ratPolysVanishingOnMatrixSet : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, MvPolynomial.coeff m f' = l (MvPolynomial.coeff m f)) → f' ∈ vanI Γ := by
  first | exact @GlobalTheory.ClassFin.component_mem_vanI | exact GlobalTheory.ClassFin.component_mem_vanI | (intros; apply GlobalTheory.ClassFin.component_mem_vanI <;> assumption)
