import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.FirstCoefficientLeDiv

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

/- English proof (translation)
Establish `hpos : 0 < Nat.clog p x` using `Nat.clog_pos hp (by omega)`. Establish `hk` using `Nat.pow_pred_clog_lt_self hp (by omega : 1 < x)`. Establish `hpR : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hxR : (0 : ℝ) < x` using `by positivity`. Establish `h1 : (p : ℝ) ^ (Nat.clog p x).pred < x` using `by exact_mod_cast hk`.

Establish `h2 : ((Nat.clog p x).pred : ℝ) < Real.logb p x`. Rewrite using `[Real.lt_logb_iff_rpow_lt hpR hxR, Real.rpow_natCast]`. Conclude with `h1`. Establish `h3 : Nat.clog p x = (Nat.clog p x).pred + 1` using `(Nat.succ_pred_eq_of_pos hpos).symm`. Rewrite using `[h3]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem clog_le_lg (p : ℕ) (hp : 1 < p) (x : ℕ) (hx : 2 ≤ x) : (Nat.clog p x : ℝ) ≤ Real.logb p x + 1 := by
  have hpos : 0 < Nat.clog p x := Nat.clog_pos hp (by omega)
  have hk := Nat.pow_pred_clog_lt_self hp (by omega : 1 < x)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hxR : (0 : ℝ) < x := by positivity
  have h1 : (p : ℝ) ^ (Nat.clog p x).pred < x := by exact_mod_cast hk
  have h2 : ((Nat.clog p x).pred : ℝ) < Real.logb p x := by
    rw [Real.lt_logb_iff_rpow_lt hpR hxR, Real.rpow_natCast]
    exact h1
  have h3 : Nat.clog p x = (Nat.clog p x).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  rw [h3]
  push_cast
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Establish `hm4 : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hS.hF.m4`. Use polynomial arithmetic with `[hS.hF.p_ge]`.
-/
private theorem twentyfive_le_p_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : (25 : ℝ) ≤ X.L.p := by
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hS.hF.m4
  nlinarith [hS.hF.p_ge]

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `hp25` using `twentyfive_le_p_of_segFacts hS`. Establish `hp1 : (1 : ℝ) < X.p` using `by show (1 : ℝ) < X.L.p`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : (1 : ℝ) ≤ X.L.a` using `hF.a1`.

Establish `ha1N : 1 ≤ X.L.a` using `by exact_mod_cast hF.a1`. Establish `hm4 : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`. Establish `hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m` using `by exact_mod_cast hF.s_le`. Establish `hyN : 8 * aBig X + X.r ≠ 0`. Apply `Nat.pos_iff_ne_zero.mp` to reduce the goal to its premises.

Unfold `aBig`. Use `Nat.mul_pos (by omega : 0 < 3 * X.s + 2) (by omega : 0 < X.L.a)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hpow` using `Nat.pow_log_le_self X.p hyN`. Establish `hyR : (0 : ℝ) < ((8 * aBig X + X.r : ℕ) : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hyN`.

Establish `hlog : ((Nat.log X.p (8 * aBig X + X.r) : ℕ) : ℝ) ≤ Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ)`. Rewrite using `[Real.le_logb_iff_rpow_le hp1 hyR, Real.rpow_natCast]`. Conclude with `hpow` after adjusting the coercions. Establish `hs0 : (0 : ℝ) ≤ X.s` using `Nat.cast_nonneg _`. Establish `hr0 : (0 : ℝ) ≤ X.r` using `Nat.cast_nonneg _`.

Establish `hyle : ((8 * aBig X + X.r : ℕ) : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r)`. Unfold `aBig`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hA : (0 : ℝ) < 8 * X.L.a + X.r` using `by linarith`.

Establish `hB : (0 : ℝ) < 3 * (X.s : ℝ) + 2` using `by linarith`. Establish `h2 : Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ) ≤ Real.logb X.p ((3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r))` using `Real.logb_le_logb_of_le hp1 hyR hyle`. Rewrite `h2` using `[Real.logb_mul hB.ne' hA.ne']`. Establish `h3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1`. Rewrite using `[Real.logb_le_iff_le_rpow hp1 hB, Real.rpow_one]`.

Use `show 3 * (X.s : ℝ) + 2 ≤ X.L.p`. Use polynomial arithmetic with `[hF.p_ge]`. Unfold `lgN lgA`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lgN_le (hS : SegFacts C0 CE1 CE2 X) : (lgN X.p (aBig X) X.r : ℝ) ≤ lgA X.p X.L.a X.r + 1 := by
  have hF := hS.hF
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hyN : 8 * aBig X + X.r ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    unfold aBig
    have := Nat.mul_pos (by omega : 0 < 3 * X.s + 2) (by omega : 0 < X.L.a)
    omega
  have hpow := Nat.pow_log_le_self X.p hyN
  have hyR : (0 : ℝ) < ((8 * aBig X + X.r : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hyN
  have hlog : ((Nat.log X.p (8 * aBig X + X.r) : ℕ) : ℝ) ≤ Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le hp1 hyR, Real.rpow_natCast]
    exact_mod_cast hpow
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  have hyle : ((8 * aBig X + X.r : ℕ) : ℝ) ≤ (3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r) := by
    unfold aBig
    push_cast
    nlinarith
  have hA : (0 : ℝ) < 8 * X.L.a + X.r := by linarith
  have hB : (0 : ℝ) < 3 * (X.s : ℝ) + 2 := by linarith
  have h2 : Real.logb X.p ((8 * aBig X + X.r : ℕ) : ℝ)
      ≤ Real.logb X.p ((3 * (X.s : ℝ) + 2) * (8 * X.L.a + X.r)) :=
    Real.logb_le_logb_of_le hp1 hyR hyle
  rw [Real.logb_mul hB.ne' hA.ne'] at h2
  have h3 : Real.logb X.p (3 * (X.s : ℝ) + 2) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow hp1 hB, Real.rpow_one]
    show 3 * (X.s : ℝ) + 2 ≤ X.L.p
    nlinarith [hF.p_ge]
  unfold lgN lgA
  push_cast
  linarith

/- English proof (translation)
Establish `hs0 : 0 ≤ s` using `le_trans ht0 hts`. Establish `hC0 : 0 ≤ (t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1` using `by nlinarith`. Establish `key` using `mul_le_mul_of_nonneg_left hL hC0`. Establish `hcoef : 2 * ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1) ≤ 3 * (s + 2) * r ^ 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hts (by linarith : (0 : ℝ) ≤ r), mul_le_mul_of_nonneg_left hr4 (by nlinarith : (0 : ℝ) ≤ (s + 2) * r)]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hcoef hlam]`.
-/
theorem initial_point_numeric_bound (t s r L lam : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s) (hr4 : 4 ≤ r) (hL : L ≤ 2 * lam)
    (hlam : 0 ≤ lam) : ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2)) * L + L ≤ 3 * (s + 2) * r ^ 2 * lam := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hC0 : 0 ≤ (t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1 := by nlinarith
  have key := mul_le_mul_of_nonneg_left hL hC0
  have hcoef : 2 * ((t + 1) * (r + 1) + ((2 * s + 1 + 1) * r + (t + 1) * 2) + 1) ≤ 3 * (s + 2) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hts (by linarith : (0 : ℝ) ≤ r),
      mul_le_mul_of_nonneg_left hr4 (by nlinarith : (0 : ℝ) ≤ (s + 2) * r)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hlam]

/- English proof (translation)
Unfold `x0N`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem initial_point_nat_cast (p A r N t : ℕ) : (x0N p A r N t : ℝ) =
    (((t : ℝ) + 1) * ((r : ℝ) + 1) + (((N : ℝ) + 1) * (r : ℝ) + ((t : ℝ) + 1) * 2)) * (lgN p A r : ℝ) := by
  unfold x0N; push_cast; ring

/- English proof (translation)
Establish `hp25` using `twentyfive_le_p_of_segFacts hS`. Establish `hp1 : (1 : ℝ) < X.p` using `by show (1 : ℝ) < X.L.p`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : (1 : ℝ) ≤ X.L.a` using `hS.hF.a1`. Establish `hr0 : (0 : ℝ) ≤ X.r` using `Nat.cast_nonneg _`.

Unfold `lgA`. Establish `: 0 ≤ Real.logb X.p (8 * X.L.a + X.r)` using `Real.logb_nonneg hp1 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem one_le_lgA_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : 1 ≤ lgA X.p X.L.a X.r := by
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have ha1 : (1 : ℝ) ≤ X.L.a := hS.hF.a1
  have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
  unfold lgA
  have : 0 ≤ Real.logb X.p (8 * X.L.a + X.r) := Real.logb_nonneg hp1 (by linarith)
  linarith

/- English proof (translation)
Establish `hF` using `hS.hF`. Rewrite using `[initial_point_nat_cast]`. Use `push_cast`. Establish `hL` using `lgN_le hS`. Establish `hlam1` using `one_le_lgA_of_segFacts hS`.

Establish `htN : (X.S C0 CE1 CE2).t ≤ X.s` using `Nat.sub_le _ _`. Establish `ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ X.s` using `by exact_mod_cast htN`. Establish `hr4 : (4 : ℝ) ≤ X.r` using `by exact_mod_cast hF.m4`. Establish `key` using `initial_point_numeric_bound ((X.S C0 CE1 CE2).t : ℝ) X.s X.r (lgN X.p (aBig X) X.r) (lgA X.p X.L.a X.r) (Nat.cast_nonneg _) ht hr4 (by linarith) (by linarith)`. Unfold `kapS`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hx_inst (hS : SegFacts C0 CE1 CE2 X) :
    (x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + lgN X.p (aBig X) X.r ≤ kapS X := by
  have hF := hS.hF
  rw [initial_point_nat_cast]
  push_cast
  have hL := lgN_le hS
  have hlam1 := one_le_lgA_of_segFacts hS
  have htN : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ X.s := by exact_mod_cast htN
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have key := initial_point_numeric_bound ((X.S C0 CE1 CE2).t : ℝ) X.s X.r (lgN X.p (aBig X) X.r) (lgA X.p X.L.a X.r)
    (Nat.cast_nonneg _) ht hr4 (by linarith) (by linarith)
  unfold kapS
  linarith

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `hmem` using `a_mem_win hS`. Unfold `flipOneThree.Inst.winA at hmem ⊢`. Rewrite using `[Nat.card_Icc]`. Establish `haF` using `(Finset.mem_Icc.mp hmem).2`.

Establish `hlt` using `Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)`. Establish `hle : ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) ≤ 2 * X.L.a` using `(Nat.floor_le hF.win0).trans hF.win_le`. Establish `hleN : ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ ≤ 2 * X.L.a` using `by exact_mod_cast hle`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Nat.cast_sub (by omega)]`.

Use `push_cast`. Combine the linear relations using `[hS.xa0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem win_facts (hS : SegFacts C0 CE1 CE2 X) :
    (X.L.a : ℝ) / (X.L.k * X.L.Y) ≤ (X.winA.card : ℝ) ∧ X.winA.card ≤ X.L.a + 1 := by
  have hF := hS.hF
  have hmem := a_mem_win hS
  unfold flipOneThree.Inst.winA at hmem ⊢
  rw [Nat.card_Icc]
  have haF := (Finset.mem_Icc.mp hmem).2
  have hlt := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
  have hle : ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) ≤ 2 * X.L.a :=
    (Nat.floor_le hF.win0).trans hF.win_le
  have hleN : ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ ≤ 2 * X.L.a := by exact_mod_cast hle
  constructor
  · rw [Nat.cast_sub (by omega)]
    push_cast
    linarith [hS.xa0]
  · omega

/- English proof (translation)
Establish `hY0 : 0 < Y` using `by linarith`. Establish `hk0 : 0 < k` using `by linarith`. Establish `hkY : 0 < k * Y` using `mul_pos hk0 hY0`. Establish `hp0 : 0 < p`. Establish `: 0 < k ^ 2 * Y ^ 2` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : 0 < a`. Use `mul_pos hp0 hb` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hW1 : k * Y * b' < a / (k * Y)`.

Rewrite using `[lt_div_iff₀ hkY]`. Establish `e : k * Y * b' * (k * Y) = k ^ 2 * Y ^ 2 * b'` using `by ring`. Rewrite using `[e]`. Establish `: k ^ 2 * Y ^ 2 * b' ≤ p * b'` using `mul_le_mul_of_nonneg_right hpk hb.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hkYb : 0 < k * Y * b'` using `by positivity`. Establish `hW0 : 0 < W` using `by linarith`. Use `⟨hW0, ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_div_iff₀ hW0 (by positivity)]`. Establish `h1 : J * (2 * Y) ≤ 5 * b' * Y`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hJ (by linarith : (0 : ℝ) ≤ 2 * Y)]`. Establish `h2 : 5 * b' * Y ≤ k * Y * b'`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ Y * b')]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem q_num (J W a k Y b' p : ℝ) (hY : 1 ≤ Y) (hk : 5 ≤ k) (hb : 0 < b') (hpk : k ^ 2 * Y ^ 2 ≤ p) (hpb : p * b' < a)
    (hJ : J ≤ 5 / 2 * b') (hW : a / (k * Y) ≤ W) : 0 < W ∧ J / W ≤ 1 / (2 * Y) := by
  have hY0 : 0 < Y := by linarith
  have hk0 : 0 < k := by linarith
  have hkY : 0 < k * Y := mul_pos hk0 hY0
  have hp0 : 0 < p := by
    have : 0 < k ^ 2 * Y ^ 2 := by positivity
    linarith
  have ha0 : 0 < a := by
    have := mul_pos hp0 hb
    linarith
  have hW1 : k * Y * b' < a / (k * Y) := by
    rw [lt_div_iff₀ hkY]
    have e : k * Y * b' * (k * Y) = k ^ 2 * Y ^ 2 * b' := by ring
    rw [e]
    have : k ^ 2 * Y ^ 2 * b' ≤ p * b' := mul_le_mul_of_nonneg_right hpk hb.le
    linarith
  have hkYb : 0 < k * Y * b' := by positivity
  have hW0 : 0 < W := by linarith
  refine ⟨hW0, ?_⟩
  rw [div_le_div_iff₀ hW0 (by positivity)]
  have h1 : J * (2 * Y) ≤ 5 * b' * Y := by
    nlinarith [mul_le_mul_of_nonneg_right hJ (by linarith : (0 : ℝ) ≤ 2 * Y)]
  have h2 : 5 * b' * Y ≤ k * Y * b' := by
    nlinarith [mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ Y * b')]
  linarith

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `hlam1` using `one_le_lgA_of_segFacts hS`. Establish `hr4 : (4 : ℝ) ≤ X.r` using `by exact_mod_cast hF.m4`. Establish `hs0 : (0 : ℝ) ≤ X.s` using `Nat.cast_nonneg _`. Establish `hc : 1 ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2` using `by nlinarith`.

Establish `hk : lgA X.p X.L.a X.r ≤ kapS X`. Unfold `kapS`. Use the polynomial consequences of the given equalities and inequalities. Establish `hk0 : 0 < kapS X` using `by linarith`. Use `⟨hk, hk0, ?_⟩` and prove the remaining obligations.

Unfold `D1r`. Establish `ht0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ)` using `Nat.cast_nonneg _`. Establish `hY` using `hS.Y1`. Establish `h1 : 0 ≤ X.L.Y * kapS X + CM * kapS X`. Use polynomial arithmetic with `[mul_pos (by linarith : (0 : ℝ) < X.L.Y) hk0, mul_pos (by linarith : (0 : ℝ) < CM) hk0]`.

Use polynomial arithmetic with `[mul_nonneg ht0 h1, mul_le_mul_of_nonneg_right hCM hk0.le]`.
-/
theorem kap_facts (hS : SegFacts C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) :
    lgA X.p X.L.a X.r ≤ kapS X ∧ 0 < kapS X ∧ kapS X ≤ D1r C0 CE1 CE2 X CM := by
  have hF := hS.hF
  have hlam1 := one_le_lgA_of_segFacts hS
  have hr4 : (4 : ℝ) ≤ X.r := by exact_mod_cast hF.m4
  have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
  have hc : 1 ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith
  have hk : lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    nlinarith
  have hk0 : 0 < kapS X := by linarith
  refine ⟨hk, hk0, ?_⟩
  unfold D1r
  have ht0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have hY := hS.Y1
  have h1 : 0 ≤ X.L.Y * kapS X + CM * kapS X := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < X.L.Y) hk0, mul_pos (by linarith : (0 : ℝ) < CM) hk0]
  nlinarith [mul_nonneg ht0 h1, mul_le_mul_of_nonneg_right hCM hk0.le]

/- English proof (translation)
Establish `hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT` using `fun x hx => by`. Unfold `evenTops at hx`. Rewrite `hx` using `[Finset.mem_sort]`. Conclude with `(Finset.mem_filter.mp hx).1`. Establish `hmem : segNext X.L.TT X.j ∈ X.L.TT`.

Unfold `segNext`. Conclude with `hmemT _ (List.get_mem _ _)`. Conclude with `hS.hF.bT_le _ hmem`.
-/
private theorem bPlus_le_five_halves_mul_b' (hS : SegFacts C0 CE1 CE2 X) :
    ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := by
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  exact hS.hF.bT_le _ hmem

/- English proof (translation)
Introduce `aTop haTop b hK J hJ`. Establish `hF` using `hS.hF`. Establish `hY1` using `hS.Y1`. Establish `hp25` using `twentyfive_le_p_of_segFacts hS`. Establish `hp1 : (1 : ℝ) < X.p` using `by show (1 : ℝ) < X.L.p`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp1N : 1 < X.p` using `by exact_mod_cast hp1`. Establish `ha1 : (1 : ℝ) ≤ X.L.a` using `hF.a1`. Establish `ha1N : 1 ≤ X.L.a` using `by exact_mod_cast hF.a1`. Establish `hm4 : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`.

Establish `hk5 : (5 : ℝ) ≤ X.L.k`. Unfold `ColumnSystems.Loc.k`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hlk, hk0, hkD⟩` from `kap_facts hS CM hCM`. Establish `hD0 : 0 < D1r C0 CE1 CE2 X CM` using `lt_of_lt_of_le hk0 hkD`.

Use `⟨oplus_le_a hS b aTop hK, mul_nonneg (by linarith) hD0.le, ?_⟩` and prove the remaining obligations. Take `⟨hWlow, hWup⟩` from `win_facts hS`. Establish `hJR : (J : ℝ) ≤ 5 / 2 * X.L.b'` using `(Nat.cast_le.mpr hJ).trans (bPlus_le_five_halves_mul_b' hS)`. Establish `hb0` using `hF.b0`. Establish `hblt` using `hF.b_lt`.

Establish `hJa : (J : ℝ) ≤ X.L.a` using `by nlinarith`. Establish `hJaN : J + 1 ≤ X.L.a + 1`. Establish `: J ≤ X.L.a` using `by exact_mod_cast hJa`. Use linear arithmetic over natural numbers and integers. Use `⟨Nat.clog X.p (X.L.a + 1), hWup.trans (Nat.le_pow_clog hp1N _), hJaN.trans (Nat.le_pow_clog hp1N _), ?_⟩` and prove the remaining obligations.

Take `⟨hW0, hqY⟩` from `q_num (J : ℝ) (X.winA.card : ℝ) X.L.a X.L.k X.L.Y X.L.b' X.L.p hY1 hk5 hb0 hpk hblt hJR hWlow`. Establish `hq0 : 0 ≤ (J : ℝ) / (X.winA.card : ℝ)` using `div_nonneg (Nat.cast_nonneg _) hW0.le`. Establish `hh0 : (0 : ℝ) ≤ (Nat.clog X.p (X.L.a + 1) : ℝ)` using `Nat.cast_nonneg _`. Establish `hhk : (Nat.clog X.p (X.L.a + 1) : ℝ) ≤ kapS X`. Establish `h1` using `clog_le_lg X.p hp1N (X.L.a + 1) (by omega)`.

Establish `hr0 : (0 : ℝ) ≤ X.r` using `Nat.cast_nonneg _`. Establish `hlog : Real.logb X.p ((X.L.a + 1 : ℕ) : ℝ) ≤ Real.logb X.p (8 * X.L.a + X.r)` using `Real.logb_le_logb_of_le hp1 (by positivity) (by push_cast; linarith)`. Unfold `lgA at hlk`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx` using `hx_inst hS`.

Establish `hfl : ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) ≤ D1r C0 CE1 CE2 X CM` using `Int.floor_le _`. Establish `hE : X.L.Y * D1r C0 CE1 CE2 X CM ≤ ((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1` using `(Int.lt_floor_add_one _).le`. Establish `key` using `eps_num X.L.Y (D1r C0 CE1 CE2 X CM) (kapS X) ((J : ℝ) / (X.winA.card : ℝ)) (Nat.clog X.p (X.L.a + 1) : ℝ) ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ)) ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) h …`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem restWinNum_proved (hS : SegFacts C0 CE1 CE2 X) (hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ)) (CM : ℝ)
    (hCM : 1 ≤ CM) : RestWinNum C0 CE1 CE2 X CM := by
  intro aTop haTop b hK J hJ
  have hF := hS.hF
  have hY1 := hS.Y1
  have hp25 := twentyfive_le_p_of_segFacts hS
  have hp1 : (1 : ℝ) < X.p := by
    show (1 : ℝ) < X.L.p
    linarith
  have hp1N : 1 < X.p := by exact_mod_cast hp1
  have ha1 : (1 : ℝ) ≤ X.L.a := hF.a1
  have ha1N : 1 ≤ X.L.a := by exact_mod_cast hF.a1
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hk5 : (5 : ℝ) ≤ X.L.k := by
    unfold ColumnSystems.Loc.k
    linarith
  obtain ⟨hlk, hk0, hkD⟩ := kap_facts hS CM hCM
  have hD0 : 0 < D1r C0 CE1 CE2 X CM := lt_of_lt_of_le hk0 hkD
  refine ⟨oplus_le_a hS b aTop hK, mul_nonneg (by linarith) hD0.le, ?_⟩
  obtain ⟨hWlow, hWup⟩ := win_facts hS
  have hJR : (J : ℝ) ≤ 5 / 2 * X.L.b' := (Nat.cast_le.mpr hJ).trans (bPlus_le_five_halves_mul_b' hS)
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have hJa : (J : ℝ) ≤ X.L.a := by nlinarith
  have hJaN : J + 1 ≤ X.L.a + 1 := by
    have : J ≤ X.L.a := by exact_mod_cast hJa
    omega
  refine ⟨Nat.clog X.p (X.L.a + 1), hWup.trans (Nat.le_pow_clog hp1N _),
    hJaN.trans (Nat.le_pow_clog hp1N _), ?_⟩
  obtain ⟨hW0, hqY⟩ := q_num (J : ℝ) (X.winA.card : ℝ) X.L.a X.L.k X.L.Y X.L.b' X.L.p hY1 hk5 hb0 hpk hblt hJR hWlow
  have hq0 : 0 ≤ (J : ℝ) / (X.winA.card : ℝ) := div_nonneg (Nat.cast_nonneg _) hW0.le
  have hh0 : (0 : ℝ) ≤ (Nat.clog X.p (X.L.a + 1) : ℝ) := Nat.cast_nonneg _
  have hhk : (Nat.clog X.p (X.L.a + 1) : ℝ) ≤ kapS X := by
    have h1 := clog_le_lg X.p hp1N (X.L.a + 1) (by omega)
    have hr0 : (0 : ℝ) ≤ X.r := Nat.cast_nonneg _
    have hlog : Real.logb X.p ((X.L.a + 1 : ℕ) : ℝ) ≤ Real.logb X.p (8 * X.L.a + X.r) :=
      Real.logb_le_logb_of_le hp1 (by positivity) (by push_cast; linarith)
    unfold lgA at hlk
    linarith
  have hx := hx_inst hS
  have hfl : ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) ≤ D1r C0 CE1 CE2 X CM := Int.floor_le _
  have hE : X.L.Y * D1r C0 CE1 CE2 X CM ≤ ((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1 :=
    (Int.lt_floor_add_one _).le
  have key := eps_num X.L.Y (D1r C0 CE1 CE2 X CM) (kapS X) ((J : ℝ) / (X.winA.card : ℝ))
    (Nat.clog X.p (X.L.a + 1) : ℝ)
    ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ))
    ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1)
    hY1 hk0 hkD hq0 hqY hh0 hhk hx hfl hE
  calc _ = (J : ℝ) / (X.winA.card : ℝ)
        + ((x0N X.p (aBig X) X.r (2 * X.s + 1) (X.S C0 CE1 CE2).t : ℝ) + (lgN X.p (aBig X) X.r : ℝ)
          + ((⌊D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + (J : ℝ) / (X.winA.card : ℝ) * (Nat.clog X.p (X.L.a + 1) : ℝ))
          / (((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℤ) : ℝ) + 1) := by ring
    _ ≤ 5 / X.L.Y := key

end Formalism.MainNotions.G.GramWindowAlt

end
