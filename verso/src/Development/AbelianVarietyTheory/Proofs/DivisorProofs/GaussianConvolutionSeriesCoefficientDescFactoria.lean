import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
open MeasureTheory Filter Topology

namespace GlobalTheory.TermEst

/- English proof (translation)
Establish `hθ0 : 0 < θ` using `by linarith`. Establish `e1 : (2 * c * θ * s * t) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * c * θ * s * t)` using `Real.pow_div_factorial_le_exp _ (by positivity) m`. Establish `e2 : 2 * c * θ * s * t ≤ c * α * t ^ 2 + (b + c) * s ^ 2`. Establish `q1 : 0 ≤ c * (α * t - θ * s) ^ 2` using `by positivity`. Establish `q2 : c * θ ^ 2 * s ^ 2 ≤ α * (b + c) * s ^ 2`.

Conclude with `mul_le_mul_of_nonneg_right hk (by positivity)`. Establish `q3 : α * (2 * c * θ * s * t) ≤ α * (c * α * t ^ 2 + (b + c) * s ^ 2)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left q3 hα`. Establish `e3 : Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t) ≤ Real.exp (c * α * t ^ 2)`. Rewrite using `[← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)`.

Establish `hm : (0 : ℝ) < m.factorial` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * (Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t)) := by gcongr`. Use `_ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * Real.exp (c * α * t ^ 2) := by gcongr`. Use `_ = θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by ring`.
-/
lemma pointwise (b c θ α s t H : ℝ) (hc : 0 < c) (hθ : 1 ≤ θ) (hα : 0 < α)
    (hk : c * θ ^ 2 ≤ α * (b + c)) (hs : 0 ≤ s) (ht : 0 ≤ t) (hH : 0 ≤ H) (i m : ℕ) :
    (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m)) ≤
      θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by
  have hθ0 : 0 < θ := by linarith
  have e1 : (2 * c * θ * s * t) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * c * θ * s * t) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have e2 : 2 * c * θ * s * t ≤ c * α * t ^ 2 + (b + c) * s ^ 2 := by
    have q1 : 0 ≤ c * (α * t - θ * s) ^ 2 := by positivity
    have q2 : c * θ ^ 2 * s ^ 2 ≤ α * (b + c) * s ^ 2 := by
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    have q3 : α * (2 * c * θ * s * t) ≤ α * (c * α * t ^ 2 + (b + c) * s ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left q3 hα
  have e3 : Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t) ≤ Real.exp (c * α * t ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hm : (0 : ℝ) < m.factorial := by positivity
  calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * t ^ m * (Real.exp (-((b + c) * s ^ 2)) * H * s ^ (i + m))
      = ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * ((2 * c * θ * s * t) ^ m / (m.factorial : ℝ))) := by
        rw [inv_pow]; field_simp; ring
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) *
          (Real.exp (-((b + c) * s ^ 2)) * Real.exp (2 * c * θ * s * t)) := by gcongr
    _ ≤ ((2 * c * s) ^ i * H * θ⁻¹ ^ m) * Real.exp (c * α * t ^ 2) := by gcongr
    _ = θ⁻¹ ^ m * Real.exp (c * α * t ^ 2) * ((2 * c * s) ^ i * H) := by ring

/- English proof (translation)
Simplify using `only [GlobalTheory.ConvSeries.wt, norm_mul, Complex.norm_exp]`. Simplify using `only [Complex.neg_re, Complex.ofReal_re]`. Rewrite using `[mul_comm (Real.exp _) ‖h a‖, mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form.
-/
lemma norm_wt {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ) (a : E) :
    ‖GlobalTheory.ConvSeries.wt b c h a‖ = Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ := by
  simp only [GlobalTheory.ConvSeries.wt, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [mul_comm (Real.exp _) ‖h a‖, mul_assoc, ← Real.exp_add]
  ring_nf

/- English proof (translation)
Introduce `E _ _ _ _ _ b c θ α hc hθ hα hk h j i y`. Break down `lt_or_ge j i with hji | hij` into its components or cases. Rewrite using `[Nat.descFactorial_eq_zero_iff_lt.mpr hji, Nat.cast_zero, mul_zero, zero_mul, zero_mul]`. Conclude with `mul_nonneg (by positivity) (integral_nonneg fun a => by positivity)`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hij`.

Rewrite using `[Nat.add_sub_cancel_left]`. Establish `hK : (2 * c) ^ (i + m) / ((i + m).factorial : ℝ) * ((i + m).descFactorial i : ℝ) = (2 * c) ^ (i + m) / (m.factorial : ℝ)`. Use `Nat.factorial_mul_descFactorial (Nat.le_add_right i m)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel_left]`. Establish `h1 : ((i + m).factorial : ℝ) = (m.factorial : ℝ) * ((i + m).descFactorial i : ℝ)`.

Conclude with `this.symm` after adjusting the coercions. Establish `h2 : (0 : ℝ) < m.factorial` using `by positivity`. Establish `h3 : (0 : ℝ) < ((i + m).descFactorial i : ℝ)`. Establish `: (0:ℝ) < ((i + m).factorial : ℝ)` using `by positivity`. Rewrite `this` using `[h1]`.

Conclude with `pos_of_mul_pos_right this h2.le`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hK]`. Establish `hint : Integrable (fun a : E => (2 * c * ‖a‖) ^ i * ‖h a‖)`.

Use `(h.integrable_pow_mul volume i).const_mul ((2 * c) ^ i)` as an intermediate fact. Use `this.congr (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[integral_const_mul]`. Simplify using `only [norm_wt]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∫ a, θ⁻¹ ^ m * Real.exp (c * α * ‖y‖ ^ 2) * ((2 * c * ‖a‖) ^ i * ‖h a‖) := by`. Use `integral_mono_of_nonneg (Eventually.of_forall fun a => by positivity) (hint.const_mul _) (Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Conclude with `pointwise b c θ α ‖a‖ ‖y‖ ‖h a‖ hc hθ hα hk (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) i m`. Use `_ = _ := integral_const_mul _ _`.
-/
theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c θ α : ℝ), 0 < c → 1 ≤ θ → 0 < α → c * θ ^ 2 ≤ α * (b + c) →
    ∀ (h : SchwartzMap E ℂ) (j i : ℕ) (y : E),
    (2 * c) ^ j / (j.factorial : ℝ) * (j.descFactorial i : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) *
      ‖y‖ ^ (j - i) ≤ θ⁻¹ ^ (j - i) * Real.exp (c * α * ‖y‖ ^ 2) * ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ := by
  intro E _ _ _ _ _ b c θ α hc hθ hα hk h j i y
  rcases lt_or_ge j i with hji | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hji, Nat.cast_zero, mul_zero, zero_mul, zero_mul]
    exact mul_nonneg (by positivity) (integral_nonneg fun a => by positivity)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_sub_cancel_left]
    have hK : (2 * c) ^ (i + m) / ((i + m).factorial : ℝ) * ((i + m).descFactorial i : ℝ) =
        (2 * c) ^ (i + m) / (m.factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (Nat.le_add_right i m)
      rw [Nat.add_sub_cancel_left] at this
      have h1 : ((i + m).factorial : ℝ) = (m.factorial : ℝ) * ((i + m).descFactorial i : ℝ) := by
        exact_mod_cast this.symm
      have h2 : (0 : ℝ) < m.factorial := by positivity
      have h3 : (0 : ℝ) < ((i + m).descFactorial i : ℝ) := by
        have : (0:ℝ) < ((i + m).factorial : ℝ) := by positivity
        rw [h1] at this
        exact pos_of_mul_pos_right this h2.le
      rw [h1]; field_simp
    rw [hK]
    have hint : Integrable (fun a : E => (2 * c * ‖a‖) ^ i * ‖h a‖) := by
      have := (h.integrable_pow_mul volume i).const_mul ((2 * c) ^ i)
      refine this.congr (Eventually.of_forall fun a => ?_)
      simp only [mul_pow]; ring
    calc (2 * c) ^ (i + m) / (m.factorial : ℝ) * (∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ (i + m)) * ‖y‖ ^ m
        = ∫ a, (2 * c) ^ (i + m) / (m.factorial : ℝ) * ‖y‖ ^ m *
            (Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ * ‖a‖ ^ (i + m)) := by
          rw [integral_const_mul]; simp only [norm_wt]; ring
      _ ≤ ∫ a, θ⁻¹ ^ m * Real.exp (c * α * ‖y‖ ^ 2) * ((2 * c * ‖a‖) ^ i * ‖h a‖) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun a => by positivity)
            (hint.const_mul _) (Eventually.of_forall fun a => ?_)
          exact pointwise b c θ α ‖a‖ ‖y‖ ‖h a‖ hc hθ hα hk (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) i m
      _ = _ := integral_const_mul _ _

end GlobalTheory.TermEst
