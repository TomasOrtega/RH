import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialApproxPowMaximal.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.polynomial_approx_pow_maximal : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R → ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) → ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  first | exact @GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow <;> assumption)
