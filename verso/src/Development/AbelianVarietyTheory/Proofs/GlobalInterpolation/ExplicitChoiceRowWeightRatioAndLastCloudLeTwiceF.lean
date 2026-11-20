import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstMulRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSigGaps

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Take `⟨x0, h0⟩` from `GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps c 1 1 0 (by positivity) (by linarith) one_pos`. Take `⟨x1, h1⟩` from `GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 10 0 1 0 le_rfl (by linarith) one_pos`. Use `⟨max x0 x1, fun s hs hx => ?_⟩` and prove the remaining obligations. Establish `hx1 : 1 ≤ s.x` using `s.one_lt_alt.le`. Establish `hx0 : 0 < s.x` using `by linarith`.

Establish `h2` using `h0 s.x ((le_max_left _ _).trans hx)`. Establish `h3` using `h1 s.x ((le_max_right _ _).trans hx)`. Rewrite `h2`, `h3` using `[← hs]`. Simplify using `only [pow_zero, one_mul, mul_one, zero_mul, add_zero] at h2 h3`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Real.rpow_def_of_pos hx0, Scale.X', Scale.b, Scale.L, ← Real.exp_add]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `e : s.x ^ 10 = Real.exp (10 * Real.log s.x)`. Rewrite using `[show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]`. Rewrite using `[e, Scale.X']`.

Conclude with `Real.exp_le_exp.2 h3`.
-/
theorem rpow_mul_X'_le_b (eps c : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    s.x ^ c * s.X' ≤ s.b ∧ s.x ^ 10 ≤ s.X' := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps c 1 1 0 (by positivity)
    (by linarith) one_pos
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 10 0 1 0 le_rfl
    (by linarith) one_pos
  refine ⟨max x0 x1, fun s hs hx => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h2 := h0 s.x ((le_max_left _ _).trans hx)
  have h3 := h1 s.x ((le_max_right _ _).trans hx)
  rw [← hs] at h2 h3
  simp only [pow_zero, one_mul, mul_one, zero_mul, add_zero] at h2 h3
  constructor
  · rw [Real.rpow_def_of_pos hx0, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  · have e : s.x ^ 10 = Real.exp (10 * Real.log s.x) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X']
    exact Real.exp_le_exp.2 h3

/- English proof (translation)
Introduce `eps he he' C hC`. Take `⟨CN, x1, hLa⟩` from `GlobalTheory.topCount_and_lambda_bounds eps he he'`. Take `⟨x2, hx2'⟩` from `GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps 1 (2 * C.GK.La * CN ^ 2) 2 (by linarith)`. Establish `hK : 1 ≤ C.GK.La` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])`. Use `⟨0, fun cD _ => ⟨0, fun ch hch => ?_⟩⟩` and prove the remaining obligations.

Take `⟨x0, hx0⟩` from `rpow_mul_X'_le_b eps (ch + 9) he`. Use `⟨max (max x0 x1) (max x2 2), fun D L hs hx hV => ?_⟩` and prove the remaining obligations. Establish `hxa : x0 ≤ L.sc.x` using `((le_max_left _ _).trans (le_max_left _ _)).trans hx`. Establish `hxb : x1 ≤ L.sc.x` using `((le_max_right _ _).trans (le_max_left _ _)).trans hx`. Establish `hxc : x2 ≤ L.sc.x` using `((le_max_left _ _).trans (le_max_right _ _)).trans hx`.

Establish `hx2 : 2 ≤ L.sc.x` using `((le_max_right _ _).trans (le_max_right _ _)).trans hx`. Establish `hx1 : 1 ≤ L.sc.x` using `by linarith`. Establish `hxp : 0 < L.sc.x` using `by linarith`. Take `⟨⟨hn0, hn⟩, hm, -⟩` from `rankVal_crude L.sc D.R hx2 hV.ranks`. Take `⟨hb, hX⟩` from `hx0 L.sc hs hxa`.

Establish `hLa1 : L.LaG ≤ L.sc.x`. Establish `h1` using `((hLa L.sc hs hxb).2.2 C.GK hK).2`. Establish `h2` using `hx2' L.sc.x hxc`. Rewrite `h2` using `[Real.rpow_one, ← hs]`. Rewrite using `[hV.La_eq]`.

Use `h1.trans (le_trans (le_of_eq ?_) h2)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 0 < D.R.n` using `by exact_mod_cast hn0`. Conclude with `this` after adjusting the coercions.

Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `le_trans (Real.one_le_rpow hx1 (by have := L.sc.eps_pos; linarith)) hV.ranks.2.2.1.1`. Establish `hX0 : 0 < L.sc.X'` using `Real.exp_pos _`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `eb' : L.sc.b' = L.sc.x * (L.sc.b / L.sc.X')` using `by rw [Scale.b', Scale.a]; ring`. Establish `ew : L.sc.w'' D.R.n = (L.sc.b / L.sc.X') / D.R.n`.

Rewrite using `[Scale.w'', Scale.b', Scale.a]`. Clear the denominators using the available nonvanishing facts. Establish `hq0 : 0 < L.sc.b / L.sc.X'` using `div_pos hb0 hX0`. Establish `hb'0 : 0 < L.sc.b'` using `by rw [eb']; positivity`. Establish `hw0 : 0 < L.sc.w'' D.R.n` using `by rw [ew]; positivity`.

Establish `hwb' : L.sc.w'' D.R.n ≤ L.sc.b'`. Rewrite using `[ew, eb']`. Conclude with `(div_le_self hq0.le hn1).trans (le_mul_of_one_le_left hq0.le hx1)`. Establish `h8 : (8 : ℝ) ≤ L.sc.x ^ 3`. Establish `: (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3` using `by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : (1 : ℝ) ≤ L.sc.x ^ 6` using `one_le_pow₀ hx1`. Establish `hb'b : 8 * (L.sc.x ^ 6 * L.sc.b') ≤ L.sc.b`. Establish `h1 : L.sc.x ^ 10 * (L.sc.b / L.sc.X') ≤ L.sc.X' * (L.sc.b / L.sc.X')` using `by gcongr`. Establish `h2 : L.sc.X' * (L.sc.b / L.sc.X') = L.sc.b` using `by field_simp`.

Rewrite using `[eb']`. Combine the equalities or inequalities in the displayed calculation. Establish `hb'6 : L.sc.b' ≤ L.sc.x ^ 6 * L.sc.b'` using `le_mul_of_one_le_left hb'0.le h6`. Establish `heta : L.etaSz + 1 ≤ L.sc.w'' D.R.n`. Establish `hy : 1 ≤ L.sc.x ^ ch` using `Real.one_le_rpow hx1 hch`.

Establish `h1 : (⌈L.sc.x ^ ch⌉₊ : ℝ) ≤ 2 * L.sc.x ^ ch`. Use `(Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by linarith)).le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : L.etaSz ≤ L.sc.x ^ 2 * (2 * (2 * L.sc.x ^ ch))`. Rewrite using `[hV.eta_eq, h0v]`.

Use `push_cast`. Use `gcongr`. Establish `h3 : 1 ≤ L.sc.x ^ 2 * L.sc.x ^ ch` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hy`. Establish `h4 : L.sc.x ^ (ch + 9) = L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) * L.sc.x ^ 4`. Rewrite using `[Real.rpow_add hxp, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring`.

Rewrite using `[ew, le_div_iff₀ hn0, le_div_iff₀ hX0]`. Use `le_trans ?_ hb` and prove the remaining obligations. Rewrite using `[h4]`. Establish `h5 : L.etaSz + 1 ≤ 8 * (L.sc.x ^ 2 * L.sc.x ^ ch)` using `by linarith`. Establish `h7 : 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) ≤ L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch)` using `by gcongr`.

Establish `h9` using `h5.trans h7`. Use `L.etaSz_pos` as an intermediate fact. Use `gcongr`. Establish `hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (L.sc.x ^ 6 * L.sc.b')`. Introduce `t`.

Use `(hV.bT_le t).trans ?_` and prove the remaining obligations. Establish `d1 : L.sc.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1 (by have := L.sc.eps_pos; linarith)`. Establish `d0 : 0 ≤ L.sc.delta1` using `Real.rpow_nonneg hxp.le _`. Establish `e1 : L.sc.x ^ L.sc.eps ≤ L.sc.x`. Use `Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by have := L.sc.eps_lt; linarith)` as an intermediate fact.

Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `e0 : 0 ≤ L.sc.x ^ L.sc.eps` using `Real.rpow_nonneg hxp.le _`. Establish `h1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ)` using `by gcongr`. Establish `h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b'` using `div_le_self (by positivity) hk1`. Establish `h3 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' ≤ 2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b'` using `by gcongr`.

Establish `h4 : 2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' = 2 * (L.sc.x ^ 6 * L.sc.b')` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd0 : 0 ≤ L.sc.b' / L.sc.x` using `by positivity`. Establish `hd1 : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb'0.le hx1`. Establish `hwin : ∀ j τ, 1 ≤ j → j ≤ D.R.m → L.sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b`.

Introduce `j τ hj hj'`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Unfold `Host.topPlaces at h1`. Take `⟨t, htT, hteq⟩` from `Finset.mem_image.1 h1`. Take `⟨a1, a2⟩` from `L.win_top j hj hj' τ ⟨t, htT⟩ hteq.symm`.

Establish `h2` using `L.bT_ge ⟨t, htT⟩`. Establish `h3` using `hbT ⟨t, htT⟩`. Apply the tactic sequence `constructor <;> linarith`. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Take `⟨a1, a2⟩` from `L.win_thick j hj hj' τ h2`.

Apply the tactic sequence `constructor <;> linarith`. Take `⟨a1, a2⟩` from `L.win_thin j hj hj' τ ⟨(D.eTau τ).2, h1, h2⟩`. Apply the tactic sequence `constructor <;> linarith`. Use `⟨fun j j' τ τ' a1 a2 a3 a4 => ?_, fun τ hm0 => ?_⟩` and prove the remaining obligations. Establish `hXX : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b`.

Rewrite using `[Scale.X'', div_mul_cancel₀ _ hw0.ne', Scale.a]`. Establish `hXX0 : 0 ≤ L.sc.X'' D.R.n`. Rewrite using `[Scale.X'', Scale.a]`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.

Take `⟨-, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩` from `hV.hc`. Establish `hb1 : L.sc.w'' D.R.n ≤ (b1 τ : ℝ)`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Unfold `Host.topPlaces at h1`. Take `⟨t, htT, hteq⟩` from `Finset.mem_image.1 h1`.

Rewrite using `[htop τ ⟨t, htT⟩ hteq.symm]`. Establish `h2` using `L.bT_ge ⟨t, htT⟩`. Establish `h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ)`. Conclude with `Int.floor_nonneg.2 hd0` after adjusting the coercions. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Establish `h3` using `Int.le_ceil L.sc.b`. Establish `h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ)` using `by exact_mod_cast (hthick τ h2).1`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hthin τ ⟨(D.eTau τ).2, h1, h2⟩]`. Conclude with `Int.le_ceil _`. Establish `h1 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz`. Rewrite using `[hV.eta_eq]`. Use `gcongr`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[(hbj τ _).1, (hbj τ _).1, ← Rat.cast_le (K := ℝ)]`. Simplify using `only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem szRow_size_ratio : SzRow (fun C D L => (∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ') ∧ (∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩)) := by
  intro eps he he' C hC
  obtain ⟨CN, x1, hLa⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, hx2'⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps 1 (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  have hK : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  refine ⟨0, fun cD _ => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := rpow_mul_X'_le_b eps (ch + 9) he
  refine ⟨max (max x0 x1) (max x2 2), fun D L hs hx hV => ?_⟩
  have hxa : x0 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxb : x1 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxc : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, -⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hX⟩ := hx0 L.sc hs hxa
  have hLa1 : L.LaG ≤ L.sc.x := by
    have h1 := ((hLa L.sc hs hxb).2.2 C.GK hK).2
    have h2 := hx2' L.sc.x hxc
    rw [Real.rpow_one, ← hs] at h2
    rw [hV.La_eq]
    refine h1.trans (le_trans (le_of_eq ?_) h2)
    ring
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 0 < D.R.n := by exact_mod_cast hn0
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k :=
    le_trans (Real.one_le_rpow hx1 (by have := L.sc.eps_pos; linarith)) hV.ranks.2.2.1.1
  have hX0 : 0 < L.sc.X' := Real.exp_pos _
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have eb' : L.sc.b' = L.sc.x * (L.sc.b / L.sc.X') := by rw [Scale.b', Scale.a]; ring
  have ew : L.sc.w'' D.R.n = (L.sc.b / L.sc.X') / D.R.n := by
    rw [Scale.w'', Scale.b', Scale.a]; field_simp
  have hq0 : 0 < L.sc.b / L.sc.X' := div_pos hb0 hX0
  have hb'0 : 0 < L.sc.b' := by rw [eb']; positivity
  have hw0 : 0 < L.sc.w'' D.R.n := by rw [ew]; positivity
  have hwb' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    rw [ew, eb']
    exact (div_le_self hq0.le hn1).trans (le_mul_of_one_le_left hq0.le hx1)
  have h8 : (8 : ℝ) ≤ L.sc.x ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
    linarith
  have h6 : (1 : ℝ) ≤ L.sc.x ^ 6 := one_le_pow₀ hx1
  have hb'b : 8 * (L.sc.x ^ 6 * L.sc.b') ≤ L.sc.b := by
    have h1 : L.sc.x ^ 10 * (L.sc.b / L.sc.X') ≤ L.sc.X' * (L.sc.b / L.sc.X') := by gcongr
    have h2 : L.sc.X' * (L.sc.b / L.sc.X') = L.sc.b := by field_simp
    rw [eb']
    calc 8 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X')))
        ≤ L.sc.x ^ 3 * (L.sc.x ^ 6 * (L.sc.x * (L.sc.b / L.sc.X'))) := by gcongr
      _ = L.sc.x ^ 10 * (L.sc.b / L.sc.X') := by ring
      _ ≤ L.sc.b := h1.trans h2.le
  have hb'6 : L.sc.b' ≤ L.sc.x ^ 6 * L.sc.b' := le_mul_of_one_le_left hb'0.le h6
  have heta : L.etaSz + 1 ≤ L.sc.w'' D.R.n := by
    have hy : 1 ≤ L.sc.x ^ ch := Real.one_le_rpow hx1 hch
    have h1 : (⌈L.sc.x ^ ch⌉₊ : ℝ) ≤ 2 * L.sc.x ^ ch := by
      have := (Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by linarith)).le
      linarith
    have h2 : L.etaSz ≤ L.sc.x ^ 2 * (2 * (2 * L.sc.x ^ ch)) := by
      rw [hV.eta_eq, h0v]
      push_cast
      gcongr
    have h3 : 1 ≤ L.sc.x ^ 2 * L.sc.x ^ ch := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hy
    have h4 : L.sc.x ^ (ch + 9) = L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) * L.sc.x ^ 4 := by
      rw [Real.rpow_add hxp, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [ew, le_div_iff₀ hn0, le_div_iff₀ hX0]
    refine le_trans ?_ hb
    rw [h4]
    have h5 : L.etaSz + 1 ≤ 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by linarith
    have h7 : 8 * (L.sc.x ^ 2 * L.sc.x ^ ch) ≤ L.sc.x ^ 3 * (L.sc.x ^ 2 * L.sc.x ^ ch) := by gcongr
    have h9 := h5.trans h7
    have := L.etaSz_pos
    gcongr
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (L.sc.x ^ 6 * L.sc.b') := by
    intro t
    refine (hV.bT_le t).trans ?_
    have d1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by have := L.sc.eps_pos; linarith)
    have d0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have e1 : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by have := L.sc.eps_lt; linarith)
      rwa [Real.rpow_one] at this
    have e0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hxp.le _
    have h1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) := by gcongr
    have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' :=
      div_le_self (by positivity) hk1
    have h3 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x * L.sc.b' ≤
        2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' := by gcongr
    have h4 : 2 * L.sc.x ^ 4 * 1 * L.sc.x * L.sc.x * L.sc.b' = 2 * (L.sc.x ^ 6 * L.sc.b') := by ring
    linarith
  have hd0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
  have hd1 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hwin : ∀ j τ, 1 ≤ j → j ≤ D.R.m → L.sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b := by
    intro j τ hj hj'
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      obtain ⟨a1, a2⟩ := L.win_top j hj hj' τ ⟨t, htT⟩ hteq.symm
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 := hbT ⟨t, htT⟩
      constructor <;> linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · obtain ⟨a1, a2⟩ := L.win_thick j hj hj' τ h2
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := L.win_thin j hj hj' τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith
  refine ⟨fun j j' τ τ' a1 a2 a3 a4 => ?_, fun τ hm0 => ?_⟩
  · have hXX : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      rw [Scale.X'', div_mul_cancel₀ _ hw0.ne', Scale.a]
    have hXX0 : 0 ≤ L.sc.X'' D.R.n := by
      rw [Scale.X'', Scale.a]; positivity
    calc wj D j τ ≤ 2 * L.sc.b := (hwin j τ a1 a2).2
      _ ≤ L.sc.x * L.sc.b := by gcongr
      _ = L.sc.X'' D.R.n * L.sc.w'' D.R.n := hXX.symm
      _ ≤ L.sc.X'' D.R.n * wj D j' τ' := by gcongr; exact (hwin j' τ' a3 a4).1
  · obtain ⟨-, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
    have hb1 : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
      · classical
        unfold Host.topPlaces at h1
        obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
        rw [htop τ ⟨t, htT⟩ hteq.symm]
        have h2 := L.bT_ge ⟨t, htT⟩
        have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
          exact_mod_cast Int.floor_nonneg.2 hd0
        push_cast
        linarith
      · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
        · have h3 := Int.le_ceil L.sc.b
          have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
          linarith
        · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
          exact Int.le_ceil _
    have h1 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]
      gcongr
      omega
    rw [(hbj τ _).1, (hbj τ _).1, ← Rat.cast_le (K := ℝ)]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_zero,
      zero_mul, add_zero]
    linarith

end GlobalTheory.EX
