import Formalism.FilteredPoleLength.ReducedBasisBounds.FourTermSumBoundOfParameters

namespace Formalism.LatticeBaseChangeAlt

/- English proof (translation)
Introduce `d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP hD hR hκ h0 h1 h2 h3`. Establish `e1 : PP ^ 2 * (D ^ 3 * κ / T) ≤ PP ^ 2 * D ^ 3 * C * k * f * b / T`. Establish `: PP ^ 2 * D ^ 3 * C * k * f * b / T = PP ^ 2 * (D ^ 3 * (C * k * f * b) / T)` using `by ring`. Rewrite using `[this]`. Use `gcongr`.

Establish `e3 : PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) ≤ PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga`. Establish `: PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga = PP ^ 2 * ((RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga)` using `by ring`. Rewrite using `[this]`. Use `gcongr`. Establish `tot : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T ≤ f * m * b * δ₂`.

Establish `: PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) = PP ^ 2 * (D ^ 3 * κ / T) + PP ^ 2 * T * c + PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ d * (f * m * b * δ₂) := mul_le_mul_of_nonneg_left tot hd`. Use `_ = d * f * m * b * δ₂ := by ring`.
-/
theorem four_term_sum_bound : FourTermSumBound := by
  intro d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP hD hR hκ h0 h1 h2 h3
  have e1 : PP ^ 2 * (D ^ 3 * κ / T) ≤ PP ^ 2 * D ^ 3 * C * k * f * b / T := by
    have : PP ^ 2 * D ^ 3 * C * k * f * b / T = PP ^ 2 * (D ^ 3 * (C * k * f * b) / T) := by ring
    rw [this]
    gcongr
  have e3 : PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) ≤
      PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga := by
    have : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga =
        PP ^ 2 * ((RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga) := by ring
    rw [this]
    gcongr
  have tot : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T ≤
      f * m * b * δ₂ := by
    have : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) =
        PP ^ 2 * (D ^ 3 * κ / T) + PP ^ 2 * T * c + PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) := by
      ring
    rw [this]
    linarith
  calc d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T
      = d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T) := by
        ring
    _ ≤ d * (f * m * b * δ₂) := mul_le_mul_of_nonneg_left tot hd
    _ = d * f * m * b * δ₂ := by ring

/- English proof (translation)
Introduce `d PP D κ T c RR ga C k f b m δ₂ q DF g₀ hd hT hTga hPP hD hRR hq hC hk hf hb hm hδ hκ h0 hTlow hc hg₀ hTc hqlow hTPP hPP2`. Establish `hga : 0 < ga` using `lt_of_lt_of_le hT hTga`. Establish `hc0 : 0 ≤ c` using `by rw [hc]; positivity`. Establish `hK : 0 ≤ C * k * f * b` using `by positivity`. Establish `hD0 : 0 ≤ D` using `by linarith`.

Establish `hPP1 : 1 ≤ PP` using `by nlinarith`. Establish `hT1 : 1 ≤ T` using `by linarith`. Establish `hRRc : RR ^ 2 * c ≤ 1 / PP ^ 2`. Establish `hP2 : 0 < PP ^ 2` using `by positivity`. Rewrite using `[hc, le_div_iff₀ hP2]`.

Establish `e : RR ^ 2 * (RR * PP * DF ^ 2 / q) * PP ^ 2 = RR ^ 3 * PP ^ 3 * DF ^ 2 / q` using `by ring`. Rewrite using `[e, div_le_one hq]`. Establish `h34 : RR ^ 3 ≤ RR ^ 4` using `pow_le_pow_right₀ hRR (by norm_num)`. Establish `: RR ^ 3 * (PP ^ 3 * DF ^ 2) ≤ RR ^ 4 * (PP ^ 3 * DF ^ 2)` using `mul_le_mul_of_nonneg_right h34 (by positivity)`. Use polynomial arithmetic with `[this]`.

Establish `hmδ : 0 < m * δ₂` using `mul_pos hm hδ`. Establish `h1 : PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4`. Rewrite `hTlow` using `[div_le_iff₀ hmδ]`. Rewrite using `[div_le_iff₀ hT]`. Use `mul_le_mul_of_nonneg_right hTlow (mul_nonneg hf hb)` as an intermediate fact.

Use polynomial arithmetic with `[this]`. Establish `hPPq : PP ^ 2 ≤ f * m * b * δ₂ / 4`. Establish `a : PP ^ 2 * 1 ≤ PP ^ 2 * (PP * T)` using `mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)`. Use polynomial arithmetic with `[a]`. Establish `h2 : PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4`.

Establish `hTc0 : 0 ≤ T * c` using `mul_nonneg hT.le hc0`. Establish `hTc1 : T * c ≤ 1` using `by nlinarith`. Establish `: PP ^ 2 * (T * c) ≤ PP ^ 2 * 1` using `mul_le_mul_of_nonneg_left hTc1 (by positivity)`. Use polynomial arithmetic with `[this]`. Establish `hside : 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3`.

Establish `s1 : PP ^ 2 / T ≤ 1` using `(div_le_one hT).2 hTPP`. Establish `s2 : (1 : ℝ) ≤ D ^ 3` using `one_le_pow₀ hD`. Establish `s3 : PP ^ 2 * 1 ≤ PP ^ 2 * D ^ 3` using `mul_le_mul_of_nonneg_left s2 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4`.

Establish `a1 : PP ^ 2 * (RR ^ 2 * c + 1 / T) ≤ PP ^ 2 * D ^ 3`. Establish `: PP ^ 2 * (RR ^ 2 * c) ≤ PP ^ 2 * (1 / PP ^ 2)` using `mul_le_mul_of_nonneg_left hRRc (by positivity)`. Establish `e : PP ^ 2 * (1 / PP ^ 2) = 1` using `by field_simp`. Establish `e' : PP ^ 2 * (1 / T) = PP ^ 2 / T` using `by ring`. Rewrite using `[mul_add, e']`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a2 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) ≤ PP ^ 2 * D ^ 3 * (C * k * f * b)` using `mul_le_mul_of_nonneg_right a1 hK`. Combine the equalities or inequalities in the displayed calculation. Conclude with `four_term_sum_bound d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP.le hD0 (by positivity) hκ h0 h1 h2 h3`.
-/
theorem four_term_sum_bound_of_parameters : FourTermSumBoundOfParameters := by
  intro d PP D κ T c RR ga C k f b m δ₂ q DF g₀ hd hT hTga hPP hD hRR hq hC hk hf hb hm hδ
    hκ h0 hTlow hc hg₀ hTc hqlow hTPP hPP2
  have hga : 0 < ga := lt_of_lt_of_le hT hTga
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hK : 0 ≤ C * k * f * b := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hT1 : 1 ≤ T := by linarith
  have hRRc : RR ^ 2 * c ≤ 1 / PP ^ 2 := by
    have hP2 : 0 < PP ^ 2 := by positivity
    rw [hc, le_div_iff₀ hP2]
    have e : RR ^ 2 * (RR * PP * DF ^ 2 / q) * PP ^ 2 = RR ^ 3 * PP ^ 3 * DF ^ 2 / q := by ring
    rw [e, div_le_one hq]
    have h34 : RR ^ 3 ≤ RR ^ 4 := pow_le_pow_right₀ hRR (by norm_num)
    have : RR ^ 3 * (PP ^ 3 * DF ^ 2) ≤ RR ^ 4 * (PP ^ 3 * DF ^ 2) :=
      mul_le_mul_of_nonneg_right h34 (by positivity)
    nlinarith [this]
  have hmδ : 0 < m * δ₂ := mul_pos hm hδ
  have h1 : PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ hmδ] at hTlow
    rw [div_le_iff₀ hT]
    have := mul_le_mul_of_nonneg_right hTlow (mul_nonneg hf hb)
    nlinarith [this]
  have hPPq : PP ^ 2 ≤ f * m * b * δ₂ / 4 := by
    have a : PP ^ 2 * 1 ≤ PP ^ 2 * (PP * T) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [a]
  have h2 : PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 := by
    have hTc0 : 0 ≤ T * c := mul_nonneg hT.le hc0
    have hTc1 : T * c ≤ 1 := by nlinarith
    have : PP ^ 2 * (T * c) ≤ PP ^ 2 * 1 := mul_le_mul_of_nonneg_left hTc1 (by positivity)
    nlinarith [this]
  have hside : 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3 := by
    have s1 : PP ^ 2 / T ≤ 1 := (div_le_one hT).2 hTPP
    have s2 : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ hD
    have s3 : PP ^ 2 * 1 ≤ PP ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left s2 (by positivity)
    linarith
  have h3 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 := by
    have a1 : PP ^ 2 * (RR ^ 2 * c + 1 / T) ≤ PP ^ 2 * D ^ 3 := by
      have : PP ^ 2 * (RR ^ 2 * c) ≤ PP ^ 2 * (1 / PP ^ 2) :=
        mul_le_mul_of_nonneg_left hRRc (by positivity)
      have e : PP ^ 2 * (1 / PP ^ 2) = 1 := by field_simp
      have e' : PP ^ 2 * (1 / T) = PP ^ 2 / T := by ring
      rw [mul_add, e']
      linarith
    have a2 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) :=
      mul_le_mul_of_nonneg_right a1 hK
    calc PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga
        = PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga := by ring
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / ga := by gcongr
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / T := by gcongr
      _ = PP ^ 2 * D ^ 3 * C * k * f * b / T := by ring
      _ ≤ _ := h1
  exact four_term_sum_bound d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP.le hD0 (by positivity) hκ
    h0 h1 h2 h3

end Formalism.LatticeBaseChangeAlt
