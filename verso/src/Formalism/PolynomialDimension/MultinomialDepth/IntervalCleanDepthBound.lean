import Mathlib
import Formalism.PolynomialDimension.ApolarComparisonExponent
import Formalism.PolynomialDimension.MultinomialDepth.ParamsI

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

namespace IntervalBounds

open ParamsIProof

/- English proof (translation)
Take `⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24⟩` from `h`. Unfold `logScale at *`. Establish `hC0 : 0 < C` using `by linarith`. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast g4`. Establish `hN1 : (1 : ℝ) ≤ N₁` using `by exact_mod_cast g5`.

Establish `hkn : 2 * N₁ + 3 ≤ k` using `by omega`. Establish `hk : (2 : ℝ) * N₁ + 3 ≤ k` using `by exact_mod_cast hkn`. Establish `hk5 : (5 : ℝ) ≤ k` using `by linarith`. Establish `hk0 : (0 : ℝ) < k` using `by linarith`. Establish `hJ1 : (1 : ℝ) ≤ J` using `by exact_mod_cast g7`.

Establish `hJN : (J : ℝ) ≤ N` using `by exact_mod_cast g8`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hk2 : (25 : ℝ) ≤ (k : ℝ) ^ 2` using `by nlinarith only [hk5]`. Establish `hY2 : 1 ≤ Y ^ 2` using `one_le_pow₀ g2`. Establish `hkp : (k : ℝ) ^ 2 ≤ p` using `le_trans (le_mul_of_one_le_right (by positivity) hY2) g3`.

Establish `hp25 : (25 : ℝ) ≤ p` using `by linarith`. Establish `hp1 : (1 : ℝ) < p` using `by linarith`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hQ : 1 ≤ (p : ℝ) ^ G'` using `one_le_pow₀ hp1.le`. Establish `hab : (p : ℝ) * b' < a` using `(lt_div_iff₀ g17).mp g18`.

Establish `ha0 : 0 < a` using `lt_trans (by positivity) hab`. Establish `hNY : 1 ≤ (N : ℝ) * Y` using `one_le_mul_of_one_le_of_one_le hN g2`. Establish `hCN : 1 ≤ C₀ * (N₁ : ℝ) ^ 2` using `one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hN1)`. Establish `hLa0 : 0 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a`. Use `Real.log_nonneg hNY` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL0 : 0 ≤ Real.log a`. Assume the negation of the conclusion as `hneg`. Rewrite `hneg` using `[not_le]`. Establish `: C₀ * (N₁ : ℝ) ^ 2 * Real.log a < 0` using `mul_neg_of_pos_of_neg (by linarith) hneg`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : 1 ≤ a` using `(Real.log_nonneg_iff ha0).mp hL0`. Establish `hl0 : 0 ≤ Real.logb p a` using `Real.logb_nonneg hp1 ha1`. Establish `hD0 : 0 ≤ D` using `le_trans (by positivity) g22`. Establish `hcS : 8 ≤ cStar` using `by linarith`.

Establish `hNcl : 0 ≤ (N : ℝ) * cl` using `by positivity`. Establish `hncl : 0 ≤ (n' : ℝ) * cl` using `by positivity`. Establish `hX : 8 ≤ cStar + N * cl + n' * cl` using `by linarith`. Establish `hk3 : 1 ≤ (k : ℝ) ^ 3` using `one_le_pow₀ (by linarith)`. Establish `hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4` using `one_le_pow₀ hQ`.

Establish `hb1 : 1 ≤ b'` using `le_trans (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hk3) hN) hQ4) (by linarith)) g2) g24`. Establish `hpa : (p : ℝ) ≤ a` using `le_trans (le_mul_of_one_le_right hp0.le hb1) hab.le`. Establish `hL1 : 1 ≤ Real.log a` using `one_le_log_of_three_le a (by linarith)`. Establish `hl1 : 1 ≤ Real.logb p a`. Rewrite using `[← Real.logb_self_eq_one hp1]`.

Conclude with `(Real.logb_le_logb hp1 hp0 ha0).mpr hpa`. Establish `hka : (k : ℝ) ≤ a`. Establish `: (k : ℝ) ≤ (k : ℝ) ^ 2` using `le_self_pow₀ (by linarith) (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg0 : 0 ≤ logBaseP p a k`.

Unfold `logBaseP`. Use `Real.logb_nonneg hp1 (show 1 ≤ 8 * a + k by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg : logBaseP p a k ≤ 3 * Real.logb p a`. Unfold `logBaseP`.

Establish `hh : Real.logb p (8 * a + k) ≤ Real.logb p (p * a)` using `(Real.logb_le_logb hp1 (by linarith) (by positivity)).mpr (by`. Establish `: 25 * a ≤ p * a` using `mul_le_mul_of_nonneg_right hp25 ha0.le`. Use the proof step `linarith)`. Rewrite `hh` using `[Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hLaN : (N₁ : ℝ) ^ 2 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a`. Establish `h3 : 1 ≤ C₀ * Real.log a` using `one_le_mul_of_one_le_of_one_le hC₀ hL1`. Use `le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ (N₁ : ℝ) ^ 2) h3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLa1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a` using `one_le_mul_of_one_le_of_one_le hCN hL1`.

Generalize the expression as in `C₀ * (N₁ : ℝ) ^ 2 * Real.log a = La at *`. Establish `hLa2 : 1 ≤ La ^ 2` using `one_le_pow₀ hLa1`. Establish `hNk : (N : ℝ) ≤ k`. Establish `h3 : 1 ≤ C * La ^ 2` using `one_le_mul_of_one_le_of_one_le hC hLa2`. Use `le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ N) h3` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `sq_level_le_degree : (N₁ : ℝ) ^ 2 ≤ k`. Establish `h3 : 1 ≤ C * N * La` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hN) hLa1`. Use `le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ La) h3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩`.
-/
theorem basics (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ)
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (h : PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar) :
    (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ (5 : ℝ) ≤ k ∧ (1 : ℝ) ≤ J ∧ (J : ℝ) ≤ N ∧ (25 : ℝ) ≤ p ∧
    1 ≤ (p : ℝ) ^ G' ∧ 0 < a ∧ 1 ≤ Real.log a ∧ 1 ≤ Real.logb p a ∧ 0 ≤ logBaseP p a k ∧
    logBaseP p a k ≤ 3 * Real.logb p a ∧ 1 ≤ logScale C₀ N₁ a ∧ (N : ℝ) ≤ k ∧ (N₁ : ℝ) ^ 2 ≤ k ∧
    0 ≤ D ∧ 1 ≤ b' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  unfold logScale at *
  have hC0 : 0 < C := by linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast g4
  have hN1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast g5
  have hkn : 2 * N₁ + 3 ≤ k := by omega
  have hk : (2 : ℝ) * N₁ + 3 ≤ k := by exact_mod_cast hkn
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast g7
  have hJN : (J : ℝ) ≤ N := by exact_mod_cast g8
  have hY0 : 0 < Y := by linarith
  have hk2 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk5]
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ g2
  have hkp : (k : ℝ) ^ 2 ≤ p := le_trans (le_mul_of_one_le_right (by positivity) hY2) g3
  have hp25 : (25 : ℝ) ≤ p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : 1 ≤ (p : ℝ) ^ G' := one_le_pow₀ hp1.le
  have hab : (p : ℝ) * b' < a := (lt_div_iff₀ g17).mp g18
  have ha0 : 0 < a := lt_trans (by positivity) hab
  have hNY : 1 ≤ (N : ℝ) * Y := one_le_mul_of_one_le_of_one_le hN g2
  have hCN : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hN1)
  have hLa0 : 0 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have := Real.log_nonneg hNY
    linarith
  have hL0 : 0 ≤ Real.log a := by
    by_contra hneg
    rw [not_le] at hneg
    have : C₀ * (N₁ : ℝ) ^ 2 * Real.log a < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  have ha1 : 1 ≤ a := (Real.log_nonneg_iff ha0).mp hL0
  have hl0 : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha1
  have hD0 : 0 ≤ D := le_trans (by positivity) g22
  have hcS : 8 ≤ cStar := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hX : 8 ≤ cStar + N * cl + n' * cl := by linarith
  have hk3 : 1 ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hb1 : 1 ≤ b' := le_trans
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hk3) hN) hQ4)
      (by linarith)) g2) g24
  have hpa : (p : ℝ) ≤ a := le_trans (le_mul_of_one_le_right hp0.le hb1) hab.le
  have hL1 : 1 ≤ Real.log a := one_le_log_of_three_le a (by linarith)
  have hl1 : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0 ha0).mpr hpa
  have hka : (k : ℝ) ≤ a := by
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hlg0 : 0 ≤ logBaseP p a k := by
    unfold logBaseP
    have := Real.logb_nonneg hp1 (show 1 ≤ 8 * a + k by linarith)
    linarith
  have hlg : logBaseP p a k ≤ 3 * Real.logb p a := by
    unfold logBaseP
    have hh : Real.logb p (8 * a + k) ≤ Real.logb p (p * a) :=
      (Real.logb_le_logb hp1 (by linarith) (by positivity)).mpr (by
        have : 25 * a ≤ p * a := mul_le_mul_of_nonneg_right hp25 ha0.le
        linarith)
    rw [Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1] at hh
    linarith
  have hLaN : (N₁ : ℝ) ^ 2 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have h3 : 1 ≤ C₀ * Real.log a := one_le_mul_of_one_le_of_one_le hC₀ hL1
    have := le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ (N₁ : ℝ) ^ 2) h3
    linarith
  have hLa1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := one_le_mul_of_one_le_of_one_le hCN hL1
  generalize C₀ * (N₁ : ℝ) ^ 2 * Real.log a = La at *
  have hLa2 : 1 ≤ La ^ 2 := one_le_pow₀ hLa1
  have hNk : (N : ℝ) ≤ k := by
    have h3 : 1 ≤ C * La ^ 2 := one_le_mul_of_one_le_of_one_le hC hLa2
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ N) h3
    linarith
  have sq_level_le_degree : (N₁ : ℝ) ^ 2 ≤ k := by
    have h3 : 1 ≤ C * N * La := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC hN) hLa1
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ La) h3
    linarith
  exact ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩

/- English proof (translation)
Establish `h1 : (k - 1) ^ 2 ≤ k ^ 2` using `by nlinarith`. Conclude with `le_trans h (mul_le_mul_of_nonneg_right h1 hlg)`.
-/
theorem log_size_bound_le (k lg kap1 : ℝ) (hk : 1 ≤ k) (hlg : 0 ≤ lg) (h : kap1 ≤ (k - 1) ^ 2 * lg) :
    kap1 ≤ k ^ 2 * lg := by
  have h1 : (k - 1) ^ 2 ≤ k ^ 2 := by nlinarith
  exact le_trans h (mul_le_mul_of_nonneg_right h1 hlg)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ ∑ y ∈ T, g y + Nr * e := by`. Use `mul_le_mul_of_nonneg_right hT he` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_shift {ι : Type} (T : Finset ι) (f g : ι → ℝ) (e Nr : ℝ) (he : 0 ≤ e)
    (hT : (T.card : ℝ) ≤ Nr) (h : ∀ y ∈ T, f y ≤ g y + e) :
    ∑ y ∈ T, f y ≤ ∑ y ∈ T, g y + Nr * e := by
  calc ∑ y ∈ T, f y ≤ ∑ y ∈ T, (g y + e) := Finset.sum_le_sum h
    _ = ∑ y ∈ T, g y + T.card * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ T, g y + Nr * e := by
        have := mul_le_mul_of_nonneg_right hT he
        linarith

end IntervalBounds

open ParamsIProof IntervalBounds

/- English proof (translation)
Introduce `CW C1 hCW hC1`. Use `⟨3 * C1 + 1000 * CW + 1002, by linarith, ?_⟩` and prove the remaining obligations. Introduce `C₀ hC₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar h mH mHp hmH hmHp`. Take `⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩` from `basics _ C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar (by linarith) hC₀ h`. Take `⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24⟩` from `h`.

Generalize the expression as in `hCdef : 3 * C1 + 1000 * CW + 1002 = C at *`. Establish `hC0 : 0 < C` using `by linarith`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hk0 : (0 : ℝ) < k` using `by linarith`. Establish `hNcl : 0 ≤ (N : ℝ) * cl` using `by positivity`.

Establish `hncl : 0 ≤ (n' : ℝ) * cl` using `by positivity`. Establish `hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4` using `one_le_pow₀ hQ`. Establish `hM : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ b'`. Establish `e1 : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `e2 : C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) ≤ C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) * (N * ((p : ℝ) ^ G') ^ 4)` using `le_mul_of_one_le_right (mul_nonneg (by positivity) (by linarith)) (one_le_mul_of_one_le_of_one_le hN hQ4)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsh` using `share C k Y (N * cl) a b' Ib Yb N (logScale C₀ N₁ a) (Real.log a) (by linarith) (by linarith) g2 hNcl hM g17 (by linarith) hN hLa1 hL1 g16 g12`. Establish `hcn` using `cnkc C (CW + 1) k Y N cl b' (by linarith) (by linarith) (by linarith) g2 (by linarith) g20 g17 hM`. Establish `hcn2 : CW * N * k * (2 * cl) / b' ≤ (CW + 1) * N * k * (2 * cl) / b'`. Apply `div_le_div_of_nonneg_right _ g17.le` to reduce the goal to its premises.

Establish `: 0 ≤ (N : ℝ) * k * (2 * cl)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : 1 / (a / ((k : ℝ) * Y)) = k * Y / a` using `one_div_div _ _`. Rewrite using `[hinv]`. Establish `hNN : 1 ≤ (N : ℝ) * N₁` using `one_le_mul_of_one_le_of_one_le hN hN1`.

Establish `hY1 : 1 / Y ≤ (N : ℝ) * N₁ / Y` using `div_le_div_of_nonneg_right hNN hY0.le`. Establish `hZ : 0 ≤ (N : ℝ) * N₁ / Y` using `by positivity`. Establish `e1 : C1 * N * N₁ / Y = C1 * ((N : ℝ) * N₁ / Y)` using `by ring`. Establish `e2 : C * N * N₁ / Y = C * ((N : ℝ) * N₁ / Y)` using `by ring`. Establish `e3 : (3 * C1 + 2) * ((N : ℝ) * N₁ / Y) ≤ C * ((N : ℝ) * N₁ / Y)` using `mul_le_mul_of_nonneg_right (by linarith) hZ`.

Rewrite `hmH`, `hmHp` using `[e1]`. Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interval_kappa_bound : KapI := by
  intro CW C1 hCW hC1
  refine ⟨3 * C1 + 1000 * CW + 1002, by linarith, ?_⟩
  intro C₀ hC₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar h mH mHp hmH hmHp
  obtain ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩ :=
    basics _ C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar (by linarith) hC₀ h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  generalize hCdef : 3 * C1 + 1000 * CW + 1002 = C at *
  have hC0 : 0 < C := by linarith
  have hY0 : 0 < Y := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hM : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ b' := by
    have e1 : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) ≤
        C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) * (N * ((p : ℝ) ^ G') ^ 4) :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) (by linarith))
        (one_le_mul_of_one_le_of_one_le hN hQ4)
    linarith
  have hsh := share C k Y (N * cl) a b' Ib Yb N (logScale C₀ N₁ a) (Real.log a) (by linarith)
    (by linarith) g2 hNcl hM g17 (by linarith) hN hLa1 hL1 g16 g12
  have hcn := cnkc C (CW + 1) k Y N cl b' (by linarith) (by linarith) (by linarith) g2
    (by linarith) g20 g17 hM
  have hcn2 : CW * N * k * (2 * cl) / b' ≤ (CW + 1) * N * k * (2 * cl) / b' := by
    apply div_le_div_of_nonneg_right _ g17.le
    have : 0 ≤ (N : ℝ) * k * (2 * cl) := by positivity
    linarith
  have hinv : 1 / (a / ((k : ℝ) * Y)) = k * Y / a := one_div_div _ _
  rw [hinv]
  have hNN : 1 ≤ (N : ℝ) * N₁ := one_le_mul_of_one_le_of_one_le hN hN1
  have hY1 : 1 / Y ≤ (N : ℝ) * N₁ / Y := div_le_div_of_nonneg_right hNN hY0.le
  have hZ : 0 ≤ (N : ℝ) * N₁ / Y := by positivity
  have e1 : C1 * N * N₁ / Y = C1 * ((N : ℝ) * N₁ / Y) := by ring
  have e2 : C * N * N₁ / Y = C * ((N : ℝ) * N₁ / Y) := by ring
  have e3 : (3 * C1 + 2) * ((N : ℝ) * N₁ / Y) ≤ C * ((N : ℝ) * N₁ / Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  rw [e1] at hmH hmHp
  rw [e2]
  linarith

end Formalism.CountingSumsFrames
