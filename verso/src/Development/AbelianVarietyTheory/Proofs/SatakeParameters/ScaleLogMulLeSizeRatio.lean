import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Introduce `eps C A heps hC hA`. Establish `hK : 0 ≤ C * (A + 1)` using `by positivity`. Establish `hev : ∀ᶠ t in Filter.atTop, t ^ ⌈6 / eps⌉₊ * Real.exp (-t) ≤ 1 / (C * (A + 1) + 1)` using `(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈6 / eps⌉₊).eventually (ge_mem_nhds (by positivity))`. Take `⟨T0, hT0⟩` from `Filter.eventually_atTop.mp hev`. Use `⟨max T0 1 ^ (3 / eps), fun s hse hx => ?_⟩` and prove the remaining obligations.

Establish `hx1 : 1 < s.x` using `s.one_lt_alt`. Establish `hx0 : 0 ≤ s.x` using `by linarith`. Establish `hT1 : 0 ≤ max T0 1` using `le_trans zero_le_one (le_max_right _ _)`. Establish `ht : max T0 1 ≤ s.x ^ (eps / 3)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.rpow_mul hT1]`. Rewrite using `[show 3 / eps * (eps / 3) = 1 by field_simp, Real.rpow_one]`. Use `_ ≤ s.x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)`. Establish `ht1 : 1 ≤ s.x ^ (eps / 3)` using `le_trans (le_max_right _ _) ht`. Establish `hxsq : s.x ^ 2 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊`.

Establish `e : s.x ^ 2 = (s.x ^ (eps / 3)) ^ (6 / eps)`. Rewrite using `[← Real.rpow_mul hx0, show eps / 3 * (6 / eps) = ((2 : ℕ) : ℝ) by field_simp; norm_num, Real.rpow_natCast]`. Rewrite using `[e, ← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil _)`. Establish `hu` using `hT0 _ (le_trans (le_max_left _ _) ht)`.

Rewrite `hu` using `[le_div_iff₀ (by positivity)]`. Establish `hu0 : 0 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3)))` using `by positivity`. Establish `he` using `Real.exp_pos (s.x ^ (eps / 3))`. Establish `e1 : (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ = (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) * Real.exp (s.x ^ (eps / 3))`. Rewrite using `[mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]`.

Establish `hlog : A * Real.log s.x + 1 ≤ (A + 1) * s.x`. Use `Real.log_le_sub_one_of_pos (by linarith : 0 < s.x)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `main : C * (A * Real.log s.x + 1) * s.x ≤ Real.exp (s.x ^ (eps / 3))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e1]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hu he.le, mul_nonneg hu0 he.le]`. Establish `hb : 0 ≤ s.b` using `(Real.exp_pos _).le`. Establish `hb' : s.b' = s.x * s.b / Real.exp (s.x ^ (eps / 3))`. Simplify using `only [Scale.b', Scale.a, Scale.X', hse]`.

Rewrite using `[hb']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_one he]`. Conclude with `main`. Use `_ = s.b := one_mul _`.
-/
theorem scale_log_mul_b'_le_b : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  intro eps C A heps hC hA
  have hK : 0 ≤ C * (A + 1) := by positivity
  have hev : ∀ᶠ t in Filter.atTop, t ^ ⌈6 / eps⌉₊ * Real.exp (-t) ≤ 1 / (C * (A + 1) + 1) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ⌈6 / eps⌉₊).eventually
      (ge_mem_nhds (by positivity))
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max T0 1 ^ (3 / eps), fun s hse hx => ?_⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 ≤ s.x := by linarith
  have hT1 : 0 ≤ max T0 1 := le_trans zero_le_one (le_max_right _ _)
  have ht : max T0 1 ≤ s.x ^ (eps / 3) := by
    calc max T0 1 = (max T0 1 ^ (3 / eps)) ^ (eps / 3) := by
          rw [← Real.rpow_mul hT1]
          rw [show 3 / eps * (eps / 3) = 1 by field_simp, Real.rpow_one]
      _ ≤ s.x ^ (eps / 3) := Real.rpow_le_rpow (by positivity) hx (by positivity)
  have ht1 : 1 ≤ s.x ^ (eps / 3) := le_trans (le_max_right _ _) ht
  have hxsq : s.x ^ 2 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by
    have e : s.x ^ 2 = (s.x ^ (eps / 3)) ^ (6 / eps) := by
      rw [← Real.rpow_mul hx0, show eps / 3 * (6 / eps) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
        Real.rpow_natCast]
    rw [e, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil _)
  have hu := hT0 _ (le_trans (le_max_left _ _) ht)
  rw [le_div_iff₀ (by positivity)] at hu
  have hu0 : 0 ≤ (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) := by positivity
  have he := Real.exp_pos (s.x ^ (eps / 3))
  have e1 : (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ =
      (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ * Real.exp (-(s.x ^ (eps / 3))) * Real.exp (s.x ^ (eps / 3)) := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hlog : A * Real.log s.x + 1 ≤ (A + 1) * s.x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < s.x)
    nlinarith
  have main : C * (A * Real.log s.x + 1) * s.x ≤ Real.exp (s.x ^ (eps / 3)) := by
    calc C * (A * Real.log s.x + 1) * s.x ≤ C * ((A + 1) * s.x) * s.x := by gcongr
      _ = C * (A + 1) * s.x ^ 2 := by ring
      _ ≤ C * (A + 1) * (s.x ^ (eps / 3)) ^ ⌈6 / eps⌉₊ := by gcongr
      _ ≤ Real.exp (s.x ^ (eps / 3)) := by
          rw [e1]
          nlinarith [mul_le_mul_of_nonneg_right hu he.le, mul_nonneg hu0 he.le]
  have hb : 0 ≤ s.b := (Real.exp_pos _).le
  have hb' : s.b' = s.x * s.b / Real.exp (s.x ^ (eps / 3)) := by
    simp only [Scale.b', Scale.a, Scale.X', hse]
  rw [hb']
  calc C * (A * Real.log s.x + 1) * (s.x * s.b / Real.exp (s.x ^ (eps / 3)))
      = C * (A * Real.log s.x + 1) * s.x / Real.exp (s.x ^ (eps / 3)) * s.b := by ring
    _ ≤ 1 * s.b := by
        gcongr
        rw [div_le_one he]
        exact main
    _ = s.b := one_mul _

end GlobalTheory
