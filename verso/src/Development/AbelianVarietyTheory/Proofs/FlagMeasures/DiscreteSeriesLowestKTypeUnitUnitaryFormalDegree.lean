import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev

/- English proof (translation)
Introduce `n ε lam H _ _ σ h`. Take `⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨v, hvS, hv, -⟩` from `hS.2.2.2.1`. Establish `hn : ‖v‖ ≠ 0` using `norm_ne_zero_iff.mpr hv`.

Use `⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]`. Establish `hle : S ≤ lowKSub ε lam σ` using `le_sSup hS`. Conclude with `hle (S.smul_mem _ hvS)`. Introduce `x a b`.

Establish `hx : uMat x ∈ UJset ε` using `x.2`. Set `f : H →ₗᵢ[ℂ] H` to `⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩`. Conclude with `f.inner_map_map a b`. Introduce `c d w hc hw hF`. Take `⟨hd, hI⟩` from `hF`.

Establish `h1` using `(hI w w w w).2`. Establish `hc' : (0 : ℝ) < (c : ℝ)` using `hc`. Establish `hww : ⟪w, w⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hw]`. Simplify using the standard rewrite rules.

Establish `hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g)) = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `g`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite `h1` using `[hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal, Complex.real_smul]`. Establish `h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d`.

Conclude with `h1` after adjusting the coercions. Establish `h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d)`. Clear denominators, using `at h2 ⊢` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `fdegOf`.

Rewrite using `[h3, hw]`. Simplify using the standard rewrite rules.
-/
theorem isDS_lowUnit_unitary_fdegOf : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  intro n ε lam H _ _ σ h
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hvS, hv, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hle : S ≤ lowKSub ε lam σ := le_sSup hS
      exact hle (S.smul_mem _ hvS)
  · intro x a b
    have hx : uMat x ∈ UJset ε := x.2
    let f : H →ₗᵢ[ℂ] H := ⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩
    exact f.inner_map_map a b
  · intro c d w hc hw hF
    obtain ⟨hd, hI⟩ := hF
    have h1 := (hI w w w w).2
    have hc' : (0 : ℝ) < (c : ℝ) := hc
    have hww : ⟪w, w⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g))
        = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal,
      Complex.real_smul] at h1
    have h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d := by
      exact_mod_cast h1
    have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d) := by
      field_simp at h2 ⊢
      linarith
    unfold fdegOf
    rw [h3, hw]
    simp

end GlobalTheory.RowLev
