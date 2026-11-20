import Mathlib
open MeasureTheory Filter Topology Set

namespace GlobalTheory

/- English proof (translation)
Take `⟨b, hbdef⟩ : ∃ b : ℝ, b = c / 2` from `⟨_, rfl⟩`. Establish `hb : 0 < b` using `by rw [hbdef]; positivity`. Establish `hI : IntegrableOn (fun s : ℝ => ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s)) (Ioi 0)` using `(exp_neg_integrableOn_Ioi 0 hb).const_mul _`. Use `Integrable.mono' hI ?_ ?_` and prove the remaining obligations. Conclude with `(Continuous.aestronglyMeasurable (by fun_prop))`.

Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)` and prove the remaining obligations. Establish `hs0 : (0:ℝ) ≤ s` using `le_of_lt hs`. Establish `h1` using `Real.pow_div_factorial_le_exp (b * (1 + s)) (mul_nonneg hb.le (by linarith)) m`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))]`. Establish `hf : (0:ℝ) < m.factorial` using `by exact_mod_cast m.factorial_pos`.

Rewrite `h1` using `[div_le_iff₀ hf, mul_pow]`. Establish `key : (1 + s) ^ m ≤ (m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s))`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]`. Combine the linear relations using `[h1]`. Establish `he : Real.exp (b * (1 + s)) = Real.exp b * Real.exp (b * s)`.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `hcs : Real.exp (-c * s) * Real.exp (b * s) = Real.exp (-b * s)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Rewrite using `[hbdef]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[he]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s) := by rw [hcs]`.
-/
theorem vertRay_expPow_weight_integrableOn (c : ℝ) (m : ℕ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-c * s) * (1 + s) ^ m) (Ioi 0) := by
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = c / 2 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; positivity
  have hI : IntegrableOn (fun s : ℝ =>
      ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine Integrable.mono' hI ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    have h1 := Real.pow_div_factorial_le_exp (b * (1 + s)) (mul_nonneg hb.le (by linarith)) m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _))]
    have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [div_le_iff₀ hf, mul_pow] at h1
    have key : (1 + s) ^ m ≤ (m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb m)]
      linarith [h1]
    have he : Real.exp (b * (1 + s)) = Real.exp b * Real.exp (b * s) := by
      rw [← Real.exp_add]; ring_nf
    have hcs : Real.exp (-c * s) * Real.exp (b * s) = Real.exp (-b * s) := by
      rw [← Real.exp_add]; congr 1; rw [hbdef]; ring
    calc Real.exp (-c * s) * (1 + s) ^ m
        ≤ Real.exp (-c * s) * ((m.factorial : ℝ) / b ^ m * Real.exp (b * (1 + s))) :=
          mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * (Real.exp (-c * s) * Real.exp (b * s)) := by
          rw [he]; ring
      _ = ((m.factorial : ℝ) / b ^ m * Real.exp b) * Real.exp (-b * s) := by rw [hcs]

/- English proof (translation)
Introduce `g K c m τ hg hc hb hτ`. Establish `hK : 0 ≤ K`. Establish `h` using `hb Complex.I (by simp)`. Establish `hpos : 0 < Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m` using `by positivity`. Assume the negation of the conclusion as `hneg`.

Establish `hneg' : K < 0` using `not_le.mp hneg`. Establish `: K * Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m < 0`. Rewrite using `[mul_assoc]`. Conclude with `mul_neg_of_neg_of_pos hneg' hpos`. Combine the linear relations using `[norm_nonneg (g Complex.I)]`.

Take `⟨A, hA⟩ : ∃ A : ℝ, A = K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m` from `⟨_, rfl⟩`. Rewrite using `[← hA]`. Establish `hw` using `vertRay_expPow_weight_integrableOn c m hc`. Establish `hbound : ∀ s : ℝ, 0 < s → ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m)`. Introduce `s hs`.

Establish `him : (τ + s * Complex.I).im = τ.im + s` using `by simp`. Establish `h1` using `hb (τ + s * Complex.I) (by rw [him]; linarith)`. Rewrite `h1` using `[him]`. Establish `hn : ‖τ + s * Complex.I‖ ≤ ‖τ‖ + s`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]`. Establish `hp : (1 + ‖τ + s * Complex.I‖) ^ m ≤ (1 + ‖τ‖) ^ m * (1 + s) ^ m`. Rewrite using `[← mul_pow]`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg (norm_nonneg τ) hs.le]`.

Establish `he : Real.exp (-c * (τ.im + s)) = Real.exp (-c * τ.im) * Real.exp (-c * s)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Establish `hmeas : AEStronglyMeasurable (fun s : ℝ => g (τ + s * Complex.I)) (volume.restrict (Ioi 0))`.

Establish `hc' : ContinuousOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0)`. Use `ContinuousOn.comp (g := g) (f := fun s : ℝ => τ + s * Complex.I) hg (by fun_prop) ?_` and prove the remaining obligations. Introduce `s hs`. Establish `him : (τ + s * Complex.I).im = τ.im + s` using `by simp`. Use `show 0 < (τ + s * Complex.I).im`.

Rewrite using `[him]`. Combine the linear relations using `[mem_Ioi.mp hs]`. Conclude with `hc'.aestronglyMeasurable measurableSet_Ioi`. Establish `hae : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0:ℝ))), ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m)` using `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hbound s hs)`. Establish `hint : IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0)` using `Integrable.mono' (hw.const_mul A) hmeas hae`.

Use `⟨hint, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem vertRay_integral_expPow_bound : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ),
    ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m *
          ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  intro g K c m τ hg hc hb hτ
  have hK : 0 ≤ K := by
    have h := hb Complex.I (by simp)
    have hpos : 0 < Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m := by positivity
    by_contra hneg
    have hneg' : K < 0 := not_le.mp hneg
    have : K * Real.exp (-c * Complex.I.im) * (1 + ‖Complex.I‖) ^ m < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg' hpos
    linarith [norm_nonneg (g Complex.I)]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m := ⟨_, rfl⟩
  rw [← hA]
  have hw := vertRay_expPow_weight_integrableOn c m hc
  have hbound : ∀ s : ℝ, 0 < s →
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) := by
    intro s hs
    have him : (τ + s * Complex.I).im = τ.im + s := by simp
    have h1 := hb (τ + s * Complex.I) (by rw [him]; linarith)
    rw [him] at h1
    have hn : ‖τ + s * Complex.I‖ ≤ ‖τ‖ + s := by
      calc ‖τ + s * Complex.I‖ ≤ ‖τ‖ + ‖(s:ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖τ‖ + s := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hp : (1 + ‖τ + s * Complex.I‖) ^ m ≤ (1 + ‖τ‖) ^ m * (1 + s) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_nonneg (norm_nonneg τ) hs.le]
    have he : Real.exp (-c * (τ.im + s)) = Real.exp (-c * τ.im) * Real.exp (-c * s) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖g (τ + s * Complex.I)‖
        ≤ K * Real.exp (-c * (τ.im + s)) * (1 + ‖τ + s * Complex.I‖) ^ m := h1
      _ ≤ K * Real.exp (-c * (τ.im + s)) * ((1 + ‖τ‖) ^ m * (1 + s) ^ m) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Real.exp_pos _).le)
      _ = A * (Real.exp (-c * s) * (1 + s) ^ m) := by rw [he, hA]; ring
  have hmeas : AEStronglyMeasurable (fun s : ℝ => g (τ + s * Complex.I))
      (volume.restrict (Ioi 0)) := by
    have hc' : ContinuousOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) := by
      refine ContinuousOn.comp (g := g) (f := fun s : ℝ => τ + s * Complex.I) hg (by fun_prop) ?_
      intro s hs
      have him : (τ + s * Complex.I).im = τ.im + s := by simp
      show 0 < (τ + s * Complex.I).im
      rw [him]
      linarith [mem_Ioi.mp hs]
    exact hc'.aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0:ℝ))),
      ‖g (τ + s * Complex.I)‖ ≤ A * (Real.exp (-c * s) * (1 + s) ^ m) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hbound s hs)
  have hint : IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) :=
    Integrable.mono' (hw.const_mul A) hmeas hae
  refine ⟨hint, ?_⟩
  calc ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖
      ≤ ∫ s in Ioi (0:ℝ), A * (Real.exp (-c * s) * (1 + s) ^ m) :=
        norm_integral_le_of_norm_le (hw.const_mul A) hae
    _ = A * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := integral_const_mul A _

end GlobalTheory
