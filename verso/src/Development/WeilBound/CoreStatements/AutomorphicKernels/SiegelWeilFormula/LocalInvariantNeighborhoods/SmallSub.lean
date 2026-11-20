import Mathlib

namespace PositivityTheory.SiegelWeilFormula.OswLocFin

/- English proof (translation)
Establish `hsq : ∀ u : ℂ, ‖u‖ = 1 → u.re ^ 2 + u.im ^ 2 = 1`. Introduce `u hu`. Establish `h` using `Complex.normSq_eq_norm_sq u`. Rewrite `h` using `[hu, Complex.normSq_apply]`. Use polynomial arithmetic with `[h]`.

Establish `hnorm : ∀ k : ℕ, ‖w ^ (2 ^ k)‖ = 1` using `fun k => by rw [norm_pow, hw, one_pow]`. Establish `hstep : ∀ k : ℕ, (w ^ (2 ^ (k + 1))).re = 2 * (w ^ (2 ^ k)).re ^ 2 - 1`. Introduce `k`. Establish `e : w ^ (2 ^ (k + 1)) = w ^ (2 ^ k) * w ^ (2 ^ k)` using `by rw [← pow_add]; congr 1; ring`. Rewrite using `[e, Complex.mul_re]`.

Use `hsq _ (hnorm k)` as an intermediate fact. Use polynomial arithmetic with `[this]`. Establish `hle : ∀ k : ℕ, (w ^ (2 ^ k)).re ≤ 1` using `fun k => (Complex.re_le_norm _).trans (hnorm k).le`. Establish `hd0 : 0 ≤ 1 - w.re` using `by have := hle 0; simp at this; linarith`. Establish `hgrow : ∀ k : ℕ, ((k : ℝ) + 1) * (1 - w.re) ≤ 1 - (w ^ (2 ^ k)).re`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[hstep k]`.

Establish `h1` using `hre k`. Establish `h2` using `hle k`. Establish `h3 : 0 ≤ (1 - (w ^ (2 ^ k)).re) * (w ^ (2 ^ k)).re` using `mul_nonneg (by linarith) (by linarith)`. Use `push_cast`. Use polynomial arithmetic with `[ih, h1, h2, hd0, h3]`.

Establish `hd_eq : 1 - w.re = 0`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < 1 - w.re` using `lt_of_le_of_ne hd0 (Ne.symm hne)`. Take `⟨k, hk⟩` from `exists_nat_gt (1 / (1 - w.re))`. Establish `h1` using `hgrow k`.

Establish `h2` using `hre k`. Establish `h4` using `hle k`. Establish `: (1 : ℝ) < ((k : ℝ) + 1) * (1 - w.re)`. Rewrite `hk` using `[div_lt_iff₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre1 : w.re = 1` using `by linarith`. Establish `him : w.im = 0` using `by have := hsq w hw; rw [hre1] at this; nlinarith`. Conclude with `Complex.ext (by simp [hre1]) (by simp [him])`.
-/
theorem eq_one_of_re_pow_two (w : ℂ) (hw : ‖w‖ = 1) (hre : ∀ k : ℕ, 1 / 2 < (w ^ (2 ^ k)).re) :
    w = 1 := by
  have hsq : ∀ u : ℂ, ‖u‖ = 1 → u.re ^ 2 + u.im ^ 2 = 1 := by
    intro u hu
    have h := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at h
    nlinarith [h]
  have hnorm : ∀ k : ℕ, ‖w ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hw, one_pow]
  have hstep : ∀ k : ℕ, (w ^ (2 ^ (k + 1))).re = 2 * (w ^ (2 ^ k)).re ^ 2 - 1 := by
    intro k
    have e : w ^ (2 ^ (k + 1)) = w ^ (2 ^ k) * w ^ (2 ^ k) := by rw [← pow_add]; congr 1; ring
    rw [e, Complex.mul_re]
    have := hsq _ (hnorm k)
    nlinarith [this]
  have hle : ∀ k : ℕ, (w ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hnorm k).le
  have hd0 : 0 ≤ 1 - w.re := by have := hle 0; simp at this; linarith
  have hgrow : ∀ k : ℕ, ((k : ℝ) + 1) * (1 - w.re) ≤ 1 - (w ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k]
      have h1 := hre k
      have h2 := hle k
      have h3 : 0 ≤ (1 - (w ^ (2 ^ k)).re) * (w ^ (2 ^ k)).re :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      nlinarith [ih, h1, h2, hd0, h3]
  have hd_eq : 1 - w.re = 0 := by
    by_contra hne
    have hpos : 0 < 1 - w.re := lt_of_le_of_ne hd0 (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - w.re))
    have h1 := hgrow k
    have h2 := hre k
    have h4 := hle k
    have : (1 : ℝ) < ((k : ℝ) + 1) * (1 - w.re) := by
      rw [div_lt_iff₀ hpos] at hk; nlinarith
    linarith
  have hre1 : w.re = 1 := by linarith
  have him : w.im = 0 := by have := hsq w hw; rw [hre1] at this; nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

/- English proof (translation)
Take `⟨δ, hδ, hδc⟩` from `Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)`. Use `⟨δ / 2, half_pos hδ, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h2 : ‖(2 : K)‖ ≤ 1`. Use `IsUltrametricDist.norm_add_le_max (1 : K) 1` as an intermediate fact. Rewrite `this` using `[one_add_one_eq_two, norm_one, max_self]`.

Conclude with `this`. Establish `hsmall : ∀ k : ℕ, ‖(2 : K) ^ k * t‖ ≤ δ / 2` using `fun k => by`. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : ∀ k : ℕ, χ ((2 : K) ^ k * t) = χ t ^ (2 ^ k)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show (2 : K) ^ (k + 1) * t = (2 : K) ^ k * t + (2 : K) ^ k * t by ring, hadd, ih, ← pow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : ∀ k : ℕ, 1 / 2 < (χ t ^ (2 ^ k)).re`. Introduce `k`. Rewrite using `[← hpow k]`.

Establish `hd` using `hδc ((2 : K) ^ k * t) (by rw [dist_zero_right]; linarith [hsmall k])`. Rewrite `hd` using `[h0, dist_eq_norm]`. Use `Complex.re_le_norm (1 - χ ((2 : K) ^ k * t))` as an intermediate fact. Rewrite `this` using `[norm_sub_rev]`. Simplify using `only [Complex.sub_re, Complex.one_re] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `eq_one_of_re_pow_two (χ t) (hn t) hre`.
-/
theorem no_small_subgroups {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (χ : K → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1)
    (hn : ∀ x, ‖χ x‖ = 1) : ∃ ε > 0, ∀ t : K, ‖t‖ ≤ ε → χ t = 1 := by
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
  refine ⟨δ / 2, half_pos hδ, fun t ht => ?_⟩
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : K) 1
    rw [one_add_one_eq_two, norm_one, max_self] at this
    exact this
  have hsmall : ∀ k : ℕ, ‖(2 : K) ^ k * t‖ ≤ δ / 2 := fun k => by
    rw [norm_mul, norm_pow]
    calc ‖(2 : K)‖ ^ k * ‖t‖ ≤ 1 * ‖t‖ := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) h2
      _ ≤ δ / 2 := by rw [one_mul]; exact ht
  have hpow : ∀ k : ℕ, χ ((2 : K) ^ k * t) = χ t ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 : K) ^ (k + 1) * t = (2 : K) ^ k * t + (2 : K) ^ k * t by ring, hadd, ih, ← pow_add]
      congr 1
      ring
  have hre : ∀ k : ℕ, 1 / 2 < (χ t ^ (2 ^ k)).re := by
    intro k
    rw [← hpow k]
    have hd := hδc ((2 : K) ^ k * t) (by rw [dist_zero_right]; linarith [hsmall k])
    rw [h0, dist_eq_norm] at hd
    have := Complex.re_le_norm (1 - χ ((2 : K) ^ k * t))
    rw [norm_sub_rev] at this
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  exact eq_one_of_re_pow_two (χ t) (hn t) hre

end PositivityTheory.SiegelWeilFormula.OswLocFin
