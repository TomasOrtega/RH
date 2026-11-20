import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

/- English proof (translation)
Introduce `O _ _ a η b g hg`. Rewrite `hg`, the goal using `[Ideal.mem_span_pair]`. Take `⟨F, G, hFG⟩` from `hg`. Establish `hX : (X : PowerSeries O) ^ η ≠ 0` using `pow_ne_zero _ PowerSeries.X_ne_zero`. Distinguish the cases in `ha : a = 0`.

Substitute `ha` using the available equality. Use `⟨0, G, ?_⟩` and prove the remaining obligations. Establish `h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g`. Rewrite using `[← hFG, map_zero, mul_zero, zero_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[zero_mul, zero_add]`. Conclude with `mul_left_cancel₀ hX h1`. Establish `hdvd : (X : PowerSeries O) ^ η ∣ F`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`.

Establish `h1 : (X : PowerSeries O) ^ η ∣ F * C a`. Establish `h0 : F * C a = X ^ η * (g - G * X ^ b)`. Rewrite using `[mul_sub, ← hFG, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0]`.

Conclude with `dvd_mul_right _ _`. Rewrite `h1` using `[PowerSeries.X_pow_dvd_iff]`. Establish `h2` using `h1 m hm`. Rewrite `h2` using `[mul_comm, PowerSeries.coeff_C_mul]`. Conclude with `(mul_eq_zero.mp h2).resolve_left ha`.

Take `⟨F', rfl⟩` from `hdvd`. Use `⟨F', G, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hX` to reduce the goal to its premises. Rewrite using `[← hFG, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_span_of_X_pow_mul : CancelQ := by
  intro O _ _ a η b g hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨F, G, hFG⟩ := hg
  have hX : (X : PowerSeries O) ^ η ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, G, ?_⟩
    have h1 : (X : PowerSeries O) ^ η * (G * X ^ b) = X ^ η * g := by
      rw [← hFG, map_zero, mul_zero, zero_add, pow_add]
      ring
    rw [zero_mul, zero_add]
    exact mul_left_cancel₀ hX h1
  · have hdvd : (X : PowerSeries O) ^ η ∣ F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h1 : (X : PowerSeries O) ^ η ∣ F * C a := by
        have h0 : F * C a = X ^ η * (g - G * X ^ b) := by
          rw [mul_sub, ← hFG, pow_add]
          ring
        rw [h0]
        exact dvd_mul_right _ _
      rw [PowerSeries.X_pow_dvd_iff] at h1
      have h2 := h1 m hm
      rw [mul_comm, PowerSeries.coeff_C_mul] at h2
      exact (mul_eq_zero.mp h2).resolve_left ha
    obtain ⟨F', rfl⟩ := hdvd
    refine ⟨F', G, ?_⟩
    apply mul_left_cancel₀ hX
    rw [← hFG, pow_add]
    ring

end Formalism.TruncatedSeriesCounting.R9
