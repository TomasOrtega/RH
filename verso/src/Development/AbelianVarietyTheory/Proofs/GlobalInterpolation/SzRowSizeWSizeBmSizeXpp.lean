import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Take `⟨x1, h1⟩` from `GlobalTheory.EX.rank_basic_bounds eps he he'`. Take `⟨x2, h2⟩` from `GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)`. Take `⟨CN, x3, h3⟩` from `GlobalTheory.topCount_and_lambda_bounds eps he he'`. Take `⟨x4, h4⟩` from `GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)`. Use `⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩` and prove the remaining obligations.

Establish `hx1 : x1 ≤ L.sc.x` using `le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)`. Establish `hx2 : x2 ≤ L.sc.x` using `le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)`. Establish `hx3 : x3 ≤ L.sc.x` using `le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))`. Establish `hx4 : x4 ≤ L.sc.x` using `le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))`. Establish `hx5 : 2 ≤ L.sc.x` using `le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)`.

Take `⟨hf, hm, -⟩` from `h1 L.sc D.R hs hx1 hV.ranks`. Take `⟨-, -, -, hb', -, hw, -⟩` from `h2 L.sc hs hx2`. Take `⟨-, -, hLa⟩` from `h3 L.sc hs hx3`. Establish `hLa'` using `(hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2`. Establish `h4'` using `h4 L.sc.x hx4`.

Use `clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx`. Establish `hetaE` using `hV.eta_eq`. Establish `hLaE` using `hV.La_eq`. Establish `hbT` using `hV.bT_le`. Establish `hx0 : 0 < L.sc.x` using `by linarith`.

Establish `hone : 1 ≤ L.sc.x` using `by linarith`. Establish `hn1 : 1 ≤ D.R.n` using `D.R.ord_pos`. Establish `hfn : (D.R.f : ℝ) = 2 * D.R.n` using `by unfold Ranks.f; push_cast; ring`. Establish `hn0 : (0 : ℝ) ≤ D.R.n` using `Nat.cast_nonneg _`. Take `⟨hw1, hw2, -⟩` from `hw D.R.n hn1 (by linarith)`.

Establish `hb1 : 1 ≤ L.sc.b` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b`. Rewrite using `[Real.sqrt_eq_rpow]`. Evaluate the numerical expressions. Establish `hsq1 : 1 ≤ Real.sqrt L.sc.b` using `Real.one_le_sqrt.2 hb1`.

Rewrite `hw1` using `[hsq]`. Establish `hy1 : 1 ≤ L.sc.x ^ (max ch 0)` using `Real.one_le_rpow hone (le_max_right _ _)`. Establish `hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0)` using `Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)`. Establish `hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10`. Rewrite using `[Real.rpow_add hx0]`.

Evaluate the numerical expressions. Rewrite `hw1`, `hb'` using `[hsplit]`. Establish `hb'0 : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X'`. Use `Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))` as an intermediate fact.

Check the signs of the components of the expression. Establish `hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3`. Establish `: L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3` using `by norm_num`. Rewrite using `[← this]`. Conclude with `hf`.

Establish `hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x`. Use `Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `hxe0 : 0 ≤ L.sc.x ^ L.sc.eps` using `Real.rpow_nonneg hx0.le _`. Establish `hd1 : L.sc.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)`.

Establish `hd0 : 0 ≤ L.sc.delta1` using `Real.rpow_nonneg hx0.le _`. Establish `hLa2 : L.LaG ≤ L.sc.x ^ 2`. Establish `ha : 0 ≤ Real.log L.sc.a`. Apply `Real.log_nonneg` to reduce the goal to its premises. Unfold `Scale.a`.

Conclude with `one_le_mul_of_one_le_of_one_le hone hb1`. Establish `e1 : L.LaG ≤ G.La { C.GK with La` using `max 1 C.GK.La } L.sc := by`. Rewrite using `[hLaE]`. Unfold `G.La`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha`.

Establish `e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2` using `by norm_num`. Rewrite `h4'` using `[Real.rpow_one, e2]`. Establish `e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2`. Establish `: 0 ≤ max 1 C.GK.La` using `le_trans zero_le_one (le_max_left _ _)`. Check the signs of the components of the expression.

Establish `e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x)` using `mul_le_mul_of_nonneg_left (by linarith) e3`. Establish `e5 : G.La { C.GK with La` using `max 1 C.GK.La } L.sc ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact.

Conclude with `(show 1 ≤ D.R.k by omega)` after adjusting the coercions. Establish `hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0)`. Unfold `h0v`. Use `Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh00 : (0 : ℝ) ≤ h0v L.sc ch` using `Nat.cast_nonneg _`. Establish `heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0))`. Rewrite using `[hetaE]`. Conclude with `mul_le_mul hm hh0 hh00 hx0.le`.

Establish `hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ L.sc.x ^ 6 * L.sc.b'`. Establish `e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x`. Establish `e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3` using `hfn ▸ hf3`. Conclude with `mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)`. Establish `e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdiv : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0.le hone`. Use `clear hych hsplit hh0 hLa' h4' hw`.

Generalize the expression as in `L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta`. Establish `hp4 : (16 : ℝ) ≤ L.sc.x ^ 4`. Use `pow_le_pow_left₀ (by norm_num) hx5 4` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp6 : L.sc.x ≤ L.sc.x ^ 6` using `le_self_pow₀ hone (by norm_num)`.

Establish `hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10`. Combine the equalities or inequalities in the displayed calculation. Establish `hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10` using `le_mul_of_one_le_left (by positivity) hy1`. Establish `hyx1 : 1 ≤ y * L.sc.x ^ 10` using `by linarith`. Establish `hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`.

Establish `hB : 1 ≤ y * L.sc.x` using `one_le_mul_of_one_le_of_one_le hy1 hone`. Establish `hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10)` using `le_mul_of_one_le_left (by linarith) hsq1`. Establish `hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10)` using `mul_le_mul_of_nonneg_left (by linarith) hb'0.le`. Use `⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2, le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩` and prove the remaining obligations. Use `hbT t` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem window_scale_bounds (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (cD ch : ℝ) :
    ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L →
      2 ≤ L.sc.x ∧ Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)
  obtain ⟨CN, x3, h3⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)
  refine ⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ L.sc.x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx4 : x4 ≤ L.sc.x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx5 : 2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hf, hm, -⟩ := h1 L.sc D.R hs hx1 hV.ranks
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h2 L.sc hs hx2
  obtain ⟨-, -, hLa⟩ := h3 L.sc hs hx3
  have hLa' := (hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2
  have h4' := h4 L.sc.x hx4
  clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx
  have hetaE := hV.eta_eq
  have hLaE := hV.La_eq
  have hbT := hV.bT_le
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  obtain ⟨hw1, hw2, -⟩ := hw D.R.n hn1 (by linarith)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hsq1 : 1 ≤ Real.sqrt L.sc.b := Real.one_le_sqrt.2 hb1
  rw [hsq] at hw1
  have hy1 : 1 ≤ L.sc.x ^ (max ch 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0) := Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10 := by
    rw [Real.rpow_add hx0]; norm_num
  rw [hsplit] at hw1 hb'
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    positivity
  have hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by
    have : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by norm_num
    rw [← this]; exact hf
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)
    rwa [Real.rpow_one] at this
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hd1 : L.sc.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hLa2 : L.LaG ≤ L.sc.x ^ 2 := by
    have ha : 0 ≤ Real.log L.sc.a := by
      apply Real.log_nonneg
      unfold Scale.a
      exact one_le_mul_of_one_le_of_one_le hone hb1
    have e1 : L.LaG ≤ G.La { C.GK with La := max 1 C.GK.La } L.sc := by
      rw [hLaE]
      unfold G.La
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha
    have e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by norm_num
    rw [Real.rpow_one, e2] at h4'
    have e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 := by
      have : 0 ≤ max 1 C.GK.La := le_trans zero_le_one (le_max_left _ _)
      positivity
    have e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x) :=
      mul_le_mul_of_nonneg_left (by linarith) e3
    have e5 : G.La { C.GK with La := max 1 C.GK.La } L.sc ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'
    linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0) := by
    unfold h0v
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)
    push_cast
    linarith
  have hh00 : (0 : ℝ) ≤ h0v L.sc ch := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0)) := by
    rw [hetaE]; exact mul_le_mul hm hh0 hh00 hx0.le
  have hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      L.sc.x ^ 6 * L.sc.b' := by
    have e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x := by
      have e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3 := hfn ▸ hf3
      exact mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)
    have e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6 := by
      calc _ ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x ^ 2 :=
            mul_le_mul_of_nonneg_left hLa2 (by positivity)
        _ ≤ L.sc.x ^ 3 * 1 * L.sc.x * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := by ring
    rw [div_le_iff₀ (by linarith)]
    calc _ ≤ L.sc.x ^ 6 * L.sc.b' := mul_le_mul_of_nonneg_right e2 hb'0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hk1
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hone
  clear hych hsplit hh0 hLa' h4' hw
  generalize L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta
  have hp4 : (16 : ℝ) ≤ L.sc.x ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hx5 4
    linarith
  have hp6 : L.sc.x ≤ L.sc.x ^ 6 := le_self_pow₀ hone (by norm_num)
  have hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10 := by
    calc _ ≤ L.sc.x ^ 4 * L.sc.x ^ 6 := mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by ring
  have hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10 := le_mul_of_one_le_left (by positivity) hy1
  have hyx1 : 1 ≤ y * L.sc.x ^ 10 := by linarith
  have hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : 1 ≤ y * L.sc.x := one_le_mul_of_one_le_of_one_le hy1 hone
  have hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10) := le_mul_of_one_le_left (by linarith) hsq1
  have hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hb'0.le
  refine ⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2,
    le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩
  have := hbT t
  linarith

/- English proof (translation)
Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Use `left`. Unfold `Host.topPlaces at h1`. Take `⟨t, ht, e⟩` from `Finset.mem_image.1 h1`. Conclude with `⟨⟨t, ht⟩, e.symm⟩`.

Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Conclude with `Or.inr (Or.inl h2)`. Conclude with `Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)`.
-/
theorem place_top_or_thick_or_thin (D : D7) (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces ∨ D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

/- English proof (translation)
Introduce `eps he he' C _`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x0, h⟩` from `window_scale_bounds eps he he' C cD ch`. Use `⟨x0, fun D L hs hx hV => ?_⟩` and prove the remaining obligations. Take `⟨hx2, hW, heta, hwb, hbb, htop⟩` from `h D L hs hx hV`.

Establish `heta0` using `L.etaSz_pos`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hdiv : 0 ≤ L.sc.b' / L.sc.x` using `div_nonneg (by linarith) hx0.le`. Use `⟨hW, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ hm`.

Take `⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩` from `hV.hc`. Establish `hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ)`. Break down `place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht` into its components or cases. Rewrite using `[h1 τ t ht]`. Establish `e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ)` using `by exact_mod_cast Int.floor_nonneg.2 hdiv`.

Establish `e2` using `L.bT_ge t`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `Int.le_ceil L.sc.b`. Establish `e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ)` using `by exact_mod_cast (h2 τ ht).1`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h3 τ ht]`. Conclude with `Int.le_ceil _`. Rewrite using `[(hb τ _).1, (hb τ _).1]`. Establish `e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m` using `by exact_mod_cast Nat.sub_le _ _`.

Establish `e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz`. Rewrite using `[hV.eta_eq]`. Conclude with `mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)`. Simplify using `only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `j τ j' τ' hj1 hj2 hj1' hj2'`. Establish `hup : wj D j τ ≤ 2 * L.sc.b`. Break down `place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht` into its components or cases. Use `(L.win_top j hj1 hj2 τ t ht).2` as an intermediate fact. Use `htop t` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(L.win_thick j hj1 hj2 τ ht).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(L.win_thin j hj1 hj2 τ ht).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlo : L.sc.w'' D.R.n ≤ wj D j' τ'`. Break down `place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht` into its components or cases. Use `(L.win_top j' hj1' hj2' τ' t ht).1` as an intermediate fact. Use `L.bT_ge t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(L.win_thick j' hj1' hj2' τ' ht).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(L.win_thin j' hj1' hj2' τ' ht).1`. Establish `hw0 : 0 < L.sc.w'' D.R.n` using `by linarith`. Establish `hb0 : 0 < L.sc.b` using `by linarith`.

Establish `hX0 : 0 ≤ L.sc.X'' D.R.n`. Unfold `Scale.X'' Scale.a`. Check the signs of the components of the expression. Establish `hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b`. Unfold `Scale.X'' Scale.a`.

Conclude with `div_mul_cancel₀ _ hw0.ne'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem szRow_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  intro eps he he' C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x0, h⟩ := window_scale_bounds eps he he' C cD ch
  refine ⟨x0, fun D L hs hx hV => ?_⟩
  obtain ⟨hx2, hW, heta, hwb, hbb, htop⟩ := h D L hs hx hV
  have heta0 := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hdiv : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx0.le
  refine ⟨hW, ?_, ?_⟩
  · intro τ hm
    obtain ⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩ := hV.hc
    have hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · rw [h1 τ t ht]
        have e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 hdiv
        have e2 := L.bT_ge t
        push_cast
        linarith
      · have e1 := Int.le_ceil L.sc.b
        have e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (h2 τ ht).1
        linarith
      · rw [h3 τ ht]; exact Int.le_ceil _
    rw [(hb τ _).1, (hb τ _).1]
    have e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast Nat.sub_le _ _
    have e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]; exact mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro j τ j' τ' hj1 hj2 hj1' hj2'
    have hup : wj D j τ ≤ 2 * L.sc.b := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j hj1 hj2 τ t ht).2
        have := htop t
        linarith
      · have := (L.win_thick j hj1 hj2 τ ht).2
        linarith
      · have := (L.win_thin j hj1 hj2 τ ht).2
        linarith
    have hlo : L.sc.w'' D.R.n ≤ wj D j' τ' := by
      rcases place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j' hj1' hj2' τ' t ht).1
        have := L.bT_ge t
        linarith
      · have := (L.win_thick j' hj1' hj2' τ' ht).1
        linarith
      · exact (L.win_thin j' hj1' hj2' τ' ht).1
    have hw0 : 0 < L.sc.w'' D.R.n := by linarith
    have hb0 : 0 < L.sc.b := by linarith
    have hX0 : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.a; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      unfold Scale.X'' Scale.a; exact div_mul_cancel₀ _ hw0.ne'
    calc wj D j τ ≤ 2 * L.sc.b := hup
      _ ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx2 hb0.le
      _ = _ := hXw.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hX0

end GlobalTheory.EX
