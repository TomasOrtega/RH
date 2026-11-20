import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

/- English proof (translation)
Introduce `E _ _ _ r X g q0 hr bas idx n`. Use `⟨?_, fun c φ x => ?_⟩` and prove the remaining obligations. Simplify using `only [Harm.rowHighest, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, MvPolynomial.mem_weightedHomogeneousSubmodule]`. Use `⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show Harm.IsHarmonic _`.

Unfold `Harm.IsHarmonic`. Introduce `t a b`. Simplify using `[Harm.laplacian]`. Simplify using `only [Harm.partOf, Finset.sum_const_zero]`. Conclude with `MvPolynomial.isWeightedHomogeneous_one _ _`.

Simplify using `only [Harm.partOf, Finset.sum_const_zero]`. Conclude with `MvPolynomial.isWeightedHomogeneous_one _ _`. Introduce `t a b _ s`. Simplify using the standard rewrite rules. Introduce `t a b _ s`.

Simplify using the standard rewrite rules. Simplify using `only [thP, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_one, Finset.sum_singleton, MvPolynomial.coeff_zero_one, one_mul]`. Establish `h0 : ∀ (k : ℕ) (hk : k = 0) (v : Fin k → (Fin n → Fin g → ℂ)), iteratedFDeriv ℂ k (thA X bas idx (c • φ) x) 0 v = thA X bas idx (c • φ) x 0`. Introduce and unpack `_ rfl v`. Conclude with `iteratedFDeriv_zero_apply v`.

Rewrite using `[h0 _ (by simp)]`. Unfold `thA thS`. Simplify using `only [Pi.zero_apply, Matrix.mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_mem_rowHighest_and_thP_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), (1 : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) ∈ Harm.rowHighest ℂ (fun _ _ => 0) (fun _ _ => 0) ∧ ∀ (c : ℂ) (φ : TF n g) (x : Frame X.Ψ r), thP X hr bas idx (c • φ) 1 x = c * (hMat X bas idx x).det ^ (n / 2) * thS φ (tauMat X bas idx x) 0 := by
  intro E _ _ _ r X g q0 hr bas idx n
  refine ⟨?_, fun c φ x => ?_⟩
  · simp only [Harm.rowHighest, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine ⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_, ?_⟩
    · show Harm.IsHarmonic _
      unfold Harm.IsHarmonic
      intro t a b
      simp [Harm.laplacian]
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · intro t a b _ s
      simp
    · intro t a b _ s
      simp
  · simp only [thP, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_one, Finset.sum_singleton,
      MvPolynomial.coeff_zero_one, one_mul]
    have h0 : ∀ (k : ℕ) (hk : k = 0) (v : Fin k → (Fin n → Fin g → ℂ)),
        iteratedFDeriv ℂ k (thA X bas idx (c • φ) x) 0 v = thA X bas idx (c • φ) x 0 := by
      rintro _ rfl v
      exact iteratedFDeriv_zero_apply v
    rw [h0 _ (by simp)]
    unfold thA thS
    simp only [Pi.zero_apply, Matrix.mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left, add_zero]
    ring

end GlobalTheory.SW
