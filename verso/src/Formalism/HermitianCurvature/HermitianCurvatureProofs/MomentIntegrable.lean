import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory Real Module
open scoped FourierTransform

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/- English proof (translation)
Establish `hC : 0 ≤ C`. Establish `h` using `(norm_nonneg _).trans (hdec 0)`. Establish `hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1))` using `by positivity`. Conclude with `nonneg_of_mul_nonneg_left h hp`. Establish `hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)))` using `(integrable_one_add_norm (by linarith)).const_mul C`.

Use `hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ 1 + ‖v‖` using `by linarith [norm_nonneg v]`. Establish `h0 : (0 : ℝ) < 1 + ‖v‖` using `by linarith`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear relations using `[norm_nonneg v]`. Conclude with `hdec v`. Use `_ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by`. Rewrite using `[Real.rpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by`. Rewrite using `[← Real.rpow_add h0]`. Use `_ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by gcongr`. Establish `: (n : ℝ) ≤ m` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem moment_integrable {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have h0 : (0 : ℝ) < 1 + ‖v‖ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ n * ‖u v‖ ≤ (1 + ‖v‖) ^ n * (C * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        gcongr
        · linarith [norm_nonneg v]
        · exact hdec v
    _ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        rw [Real.rpow_natCast]; ring
    _ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by
        rw [← Real.rpow_add h0]
    _ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by
        gcongr
        have : (n : ℝ) ≤ m := by exact_mod_cast hn
        linarith

/- English proof (translation)
Use `set g : V → ℂ := 𝓕 D with hg`. Establish `hgc : Continuous g` using `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hD`. Use `set h : V → ℂ := fun x => g (-x) with hh`. Establish `hhc : Continuous h` using `hgc.comp continuous_neg`. Establish `hhd : ∀ w, ‖h w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))`.

Introduce `w`. Use `hdec (-w)` as an intermediate fact. Rewrite `this` using `[norm_neg]`. Then use the resulting hypothesis. Establish `hmom : ∀ n : ℕ, n ≤ m → Integrable (fun v => ‖v‖ ^ n * ‖h v‖)` using `moment_integrable hhc m C hhd`. Establish `hmomN : ∀ n : ℕ, (n : ℕ∞) ≤ (m : ℕ∞) → Integrable (fun v => ‖v‖ ^ n * ‖h v‖)` using `fun n hn => hmom n (by exact_mod_cast hn)`.

Establish `hgi : Integrable g`. Use `moment_integrable hgc m C hdec 0 (Nat.zero_le _)` as an intermediate fact. Simplify using `only [pow_zero, one_mul] at this`. Conclude with `(integrable_norm_iff hgc.aestronglyMeasurable).1 this`. Establish `hinv : 𝓕 h = 𝓕⁻ g` using `(fourierInv_eq_fourier_comp_neg g).symm`.

Use `⟨𝓕 h, Real.contDiff_fourier hmomN, fun j hj => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Use `⟨∫ v, (2 * π * ‖innerSL ℝ (E := V)‖) ^ j * (‖v‖ ^ j * ‖h v‖), fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.iteratedFDeriv_fourier hmomN hhc.aestronglyMeasurable (by exact_mod_cast hj)]`. Use `(VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_` and prove the remaining obligations. Use `integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) ((hmom j hj).const_mul _) (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations.

Use `VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) h v j` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[hinv]`. Conclude with `hD.fourierInv_fourier_eq hgi ht`.
-/
theorem fourier_smooth (D : V → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ w, ‖𝓕 D w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) :
    ∃ D' : V → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  set g : V → ℂ := 𝓕 D with hg
  have hgc : Continuous g :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hD
  set h : V → ℂ := fun x => g (-x) with hh
  have hhc : Continuous h := hgc.comp continuous_neg
  have hhd : ∀ w, ‖h w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by
    intro w
    have := hdec (-w)
    rwa [norm_neg] at this
  have hmom : ∀ n : ℕ, n ≤ m → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    moment_integrable hhc m C hhd
  have hmomN : ∀ n : ℕ, (n : ℕ∞) ≤ (m : ℕ∞) → Integrable (fun v => ‖v‖ ^ n * ‖h v‖) :=
    fun n hn => hmom n (by exact_mod_cast hn)
  have hgi : Integrable g := by
    have := moment_integrable hgc m C hdec 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hgc.aestronglyMeasurable).1 this
  have hinv : 𝓕 h = 𝓕⁻ g := (fourierInv_eq_fourier_comp_neg g).symm
  refine ⟨𝓕 h, Real.contDiff_fourier hmomN, fun j hj => ?_, fun t ht => ?_⟩
  · refine ⟨∫ v, (2 * π * ‖innerSL ℝ (E := V)‖) ^ j * (‖v‖ ^ j * ‖h v‖), fun t => ?_⟩
    rw [Real.iteratedFDeriv_fourier hmomN hhc.aestronglyMeasurable (by exact_mod_cast hj)]
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
      ((hmom j hj).const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    have := VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) h v j
    simpa [mul_assoc] using this
  · rw [hinv]
    exact hD.fourierInv_fourier_eq hgi ht

end Formalism.FourierDecayAlt.P5.HerC.Fou
