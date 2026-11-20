import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExistsHigh

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

/- English proof (translation)
Establish `hY0 : 0 < Y` using `by linarith`. Establish `e1 : (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) = CM / Y + 2 * (Sr / Yr) * (lg / κ) / Y`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Establish `h1 : lg / κ ≤ 1 / 24` using `by rw [div_le_iff₀ hκ]; linarith`.

Establish `h2 : 0 ≤ Sr / Yr` using `div_nonneg hS0 hYr.le`. Establish `h3 : 0 ≤ lg / κ` using `div_nonneg hlg hκ.le`. Establish `h4 : 2 * (Sr / Yr) * (lg / κ) ≤ 2 * (7 / Y) * (1 / 24)` using `by gcongr`. Establish `h5 : 7 / Y ≤ 7` using `by rw [div_le_iff₀ hY0]; nlinarith`. Establish `h6 : 2 * (Sr / Yr) * (lg / κ) / Y ≤ 1 / Y`.

Apply `div_le_div_of_nonneg_right _ hY0.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h7 : 2 * Sr / Yr = 2 * (Sr / Yr)` using `by ring`. Rewrite using `[h7]`. Establish `h8 : 2 * (Sr / Yr) ≤ 14 / Y`.

Establish `: 2 * (7 / Y) = 14 / Y` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : (15 + CM) / Y = 14 / Y + CM / Y + 1 / Y` using `by ring`. Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eps_num (Sr Yr Y κ lg CM : ℝ) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (15 + CM) / Y := by
  have hY0 : 0 < Y := by linarith
  have e1 : (CM * κ + 2 * Sr * lg / Yr) / (Y * κ) = CM / Y + 2 * (Sr / Yr) * (lg / κ) / Y := by
    field_simp
  rw [e1]
  have h1 : lg / κ ≤ 1 / 24 := by rw [div_le_iff₀ hκ]; linarith
  have h2 : 0 ≤ Sr / Yr := div_nonneg hS0 hYr.le
  have h3 : 0 ≤ lg / κ := div_nonneg hlg hκ.le
  have h4 : 2 * (Sr / Yr) * (lg / κ) ≤ 2 * (7 / Y) * (1 / 24) := by gcongr
  have h5 : 7 / Y ≤ 7 := by rw [div_le_iff₀ hY0]; nlinarith
  have h6 : 2 * (Sr / Yr) * (lg / κ) / Y ≤ 1 / Y := by
    apply div_le_div_of_nonneg_right _ hY0.le
    nlinarith
  have h7 : 2 * Sr / Yr = 2 * (Sr / Yr) := by ring
  rw [h7]
  have h8 : 2 * (Sr / Yr) ≤ 14 / Y := by
    have : 2 * (7 / Y) = 14 / Y := by ring
    linarith
  have e2 : (15 + CM) / Y = 14 / Y + CM / Y + 1 / Y := by ring
  rw [e2]
  linarith

/- English proof (translation)
Use `(eps_num Sr Yr Y κ lg 2 hY hYr hS0 hSY hκ hlg hlk).trans ?_` and prove the remaining obligations. Apply `div_le_div_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem epsilon_bound_M_constant (Sr Yr Y κ lg CM : ℝ) (hCM : 1 ≤ CM) (hY : 1 ≤ Y) (hYr : 0 < Yr) (hS0 : 0 ≤ Sr) (hSY : Sr / Yr ≤ 7 / Y)
    (hκ : 0 < κ) (hlg : 0 ≤ lg) (hlk : 24 * lg ≤ κ) :
    2 * Sr / Yr + (2 * κ + 2 * Sr * lg / Yr) / (Y * κ) ≤ (30 + CM) / Y := by
  refine (eps_num Sr Yr Y κ lg 2 hY hYr hS0 hSY hκ hlg hlk).trans ?_
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure EpsFacts (C0 : ℝ) (X : flipOneThree.Inst) : Prop where
  pk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.p : ℝ)
  kYb : X.L.k * X.L.Y ^ 2 * X.L.b' ≤ X.L.a / 2

/- English proof (translation)
Take `⟨h0, -⟩` from `hH`. Take `⟨hY, hpk, ⟨s0, hs0, -⟩, -, -, hN1, -, -, hb0, -, -, -, -, hYb, -, hlog, -⟩` from `h0`. Establish `hN : (1 : ℝ) ≤ X.L.N`. Establish `: 1 ≤ X.L.TT.card` using `Finset.card_pos.2 ⟨s0, hs0⟩`. Use `show (1 : ℝ) ≤ (X.L.TT.card : ℝ)`.

Conclude with `this` after adjusting the coercions. Establish `hr5` using `r5 hS`. Establish `hkb` using `hS.kb`. Establish `ha100 : (100 : ℝ) ≤ X.L.a`. Establish `h25 : (25 : ℝ) ≤ ((X.r : ℝ) + 1) * X.L.b'` using `by nlinarith only [hr5, hb5]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hloga : 1 ≤ Real.log X.L.a`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hLa : 1 ≤ X.L.La C0` using `by show 1 ≤ lambdaScale C0 X.L.N1 X.L.a`. Unfold `lambdaScale`. Establish `h1 : (1 : ℝ) ≤ (X.L.N1 : ℝ)` using `by exact_mod_cast hN1`. Establish `h2 : (1 : ℝ) ≤ (X.L.N1 : ℝ) ^ 2` using `one_le_pow₀ h1`. Establish `h3` using `one_le_mul_of_one_le_of_one_le hC0 h2`.

Conclude with `one_le_mul_of_one_le_of_one_le h3 hloga`. Establish `hYb2 : (2 : ℝ) ≤ X.L.Yb` using `le_trans hCYb hYb`. Use `⟨hpk, ?_⟩` and prove the remaining obligations. Establish `h1 : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' ≤ X.L.a`. Use `mul_le_mul_of_nonneg_right hlog hb0.le` as an intermediate fact.

Rewrite `this` using `[div_mul_cancel₀ _ hb0.ne']`. Then use the resulting hypothesis. Establish `hM : 2 ≤ X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a`. Establish `h4 : (1 : ℝ) ≤ X.L.N * X.L.La C0 * Real.log X.L.a` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hLa) hloga`. Use polynomial arithmetic with `only [hYb2, h4]`. Establish `h3 : 0 ≤ X.L.k * X.L.Y ^ 2 * X.L.b'`.

Establish `: (0 : ℝ) ≤ X.L.k` using `by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity`. Use `hb0.le` as an intermediate fact. Check the signs of the components of the expression. Establish `e : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' = (X.L.k * X.L.Y ^ 2 * X.L.b') * (X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a)` using `by ring`. Rewrite `h1` using `[e]`.

Establish `h5` using `mul_le_mul_of_nonneg_left hM h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem epsFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hb5 : (X.r : ℝ) + 1 ≤ X.L.b') : EpsFacts C0 X := by
  obtain ⟨h0, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, -, hN1, -, -, hb0, -, -, -, -, hYb, -, hlog, -⟩ := h0
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hr5 := r5 hS
  have hkb := hS.kb
  have ha100 : (100 : ℝ) ≤ X.L.a := by
    have h25 : (25 : ℝ) ≤ ((X.r : ℝ) + 1) * X.L.b' := by nlinarith only [hr5, hb5]
    linarith
  have hloga : 1 ≤ Real.log X.L.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hLa : 1 ≤ X.L.La C0 := by
    show 1 ≤ lambdaScale C0 X.L.N1 X.L.a
    unfold lambdaScale
    have h1 : (1 : ℝ) ≤ (X.L.N1 : ℝ) := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ (X.L.N1 : ℝ) ^ 2 := one_le_pow₀ h1
    have h3 := one_le_mul_of_one_le_of_one_le hC0 h2
    exact one_le_mul_of_one_le_of_one_le h3 hloga
  have hYb2 : (2 : ℝ) ≤ X.L.Yb := le_trans hCYb hYb
  refine ⟨hpk, ?_⟩
  have h1 : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right hlog hb0.le
    rwa [div_mul_cancel₀ _ hb0.ne'] at this
  have hM : 2 ≤ X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a := by
    have h4 : (1 : ℝ) ≤ X.L.N * X.L.La C0 * Real.log X.L.a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hLa) hloga
    nlinarith only [hYb2, h4]
  have h3 : 0 ≤ X.L.k * X.L.Y ^ 2 * X.L.b' := by
    have : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have := hb0.le
    positivity
  have e : X.L.k * X.L.Y ^ 2 * X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a * X.L.b' =
      (X.L.k * X.L.Y ^ 2 * X.L.b') * (X.L.Yb * X.L.N * X.L.La C0 * Real.log X.L.a) := by ring
  rw [e] at h1
  have h5 := mul_le_mul_of_nonneg_left hM h3
  linarith

/- English proof (translation)
Introduce `dl hdl a ha x hx i`. Establish `hk : X.L.k = (X.r : ℝ) + 1` using `rfl`. Establish `hk0 : X.L.k ≠ 0` using `by rw [hk]; have := r5 hS; linarith`. Establish `hY0 : X.L.Y ≠ 0` using `by have := hS.Y1; linarith`. Establish `hr5` using `r5 hS`.

Establish `hY` using `hS.Y1`. Establish `hb0` using `hS.hF.b0`. Establish `hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)` using `by exact_mod_cast hS.P1 _`. Establish `hkP : ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.b'` using `hS.kP _`. Establish `hb5 : (X.r : ℝ) + 1 ≤ X.L.b'`.

Use `mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ (X.r : ℝ) + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkY0 : 0 < X.L.k * X.L.Y` using `by rw [hk]; exact mul_pos (by linarith) (by linarith)`. Establish `hE` using `hE' hb5`. Establish `hkYb` using `hE.kYb`.

Establish `h4Y : 4 * X.L.Y ≤ X.L.k * X.L.Y ^ 2` using `by rw [hk]; nlinarith only [hr5, hY]`. Establish `hYb' : 4 * X.L.Y * X.L.b' ≤ X.L.a`. Use `mul_le_mul_of_nonneg_right h4Y hb0.le` as an intermediate fact. Establish `: (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hroomR : (X.L.a : ℝ) + 2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.a + X.L.a / (X.L.k * X.L.Y) - 1`. Establish `h1 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k ≤ 3 * X.L.b'`. Rewrite using `[hk]`. Use polynomial arithmetic with `only [hkP, hb5]`. Establish `h2 : 3 * X.L.b' * X.L.Y ≤ X.L.a` using `by nlinarith only [hYb', hY, hb0]`.

Establish `h3 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) ≤ X.L.a / (X.L.k * X.L.Y)`. Rewrite using `[le_div_iff₀ hkY0]`. Establish `: (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * (X.L.k * X.L.Y) = ((2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k) * X.L.Y` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `only [h1, h2, hY]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwin : (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) - 1 < ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ)`. Use `Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)` as an intermediate fact. Use `hS.xa0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤ ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises. Use `push_cast`. Use `hS.xa0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hYl` using `Yl_bound hS hFree hdl ha hx i hroom`. Establish `hYP : X.L.a / (2 * (X.L.k * X.L.Y)) ≤ ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)`. Establish `h1 : 1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.a / (2 * (X.L.k * X.L.Y))`. Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h2 : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1) ≤ 2 * X.L.b'`.

Use polynomial arithmetic with `only [hkP, hb5]`. Rewrite using `[hk]`. Establish `: (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * (2 * (((X.r : ℝ) + 1) * X.L.Y)) = 2 * X.L.Y * ((1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1))` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `only [h2, hYb', hY]`.

Establish `h4 : X.L.a / (X.L.k * X.L.Y) = 2 * (X.L.a / (2 * (X.L.k * X.L.Y)))` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha'` using `aTopPt_mem ha`. Establish `hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a)`. Rewrite using `[← hFree dl hdl a ha _ ha']`.

Conclude with `hx`. Take `⟨hK', -, -⟩` from `digits_of_idx hx'`. Establish `hT'` using `(mem_cbox' ha').1`. Establish `hSB` using `S_bound hS _ hT' x.1 hK' x.2 i`. Establish `eS : (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i = (gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i`.

Rewrite using `[setTies_top ha hx]`. Both sides reduce to the same expression. Unfold `epsM flipOneThree.InstM.eps flipOneThree.InstM.Si flipOneThree.InstM.LLt`. Rewrite using `[eS]`. Establish `hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ)` using `hS.hF.p_ge`.

Establish `hp0 : (0 : ℝ) < X.p` using `by nlinarith only [hp, hr5]`. Establish `hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ)` using `by exact_mod_cast hS.hF.s_le`. Establish `hB2 : 0 < X.L.a / (2 * (X.L.k * X.L.Y))`. Establish `: (0 : ℝ) < X.L.a` using `by nlinarith only [hYb', hY, hb0]`. Check the signs of the components of the expression.

Establish `hYr0 : (0 : ℝ) < ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ)`. Establish `h2` using `lt_of_lt_of_le hB2 hYP`. Conclude with `pos_of_mul_pos_left h2 (by linarith)`. Establish `hB1 : 0 ≤ 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)`. Establish `: (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`.

Check the signs of the components of the expression. Establish `hfin : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y ≤ 7 * (X.L.a / (2 * (X.L.k * X.L.Y)))`. Establish `hq : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) ≤ 4 * X.L.a`. Establish `hpk'` using `hE.pk`. Establish `h1 : (2 * (X.s : ℝ) + 1) ≤ X.L.k` using `by rw [hk]; linarith`.

Establish `e3 : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) = 4 * X.L.a * ((2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2) / X.p` using `by ring`. Rewrite using `[e3, div_le_iff₀ hp0]`. Establish `h2 : (2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2 ≤ X.L.k ^ 2 * X.L.Y ^ 2`. Establish `: 0 ≤ X.L.k * X.L.Y ^ 2` using `by rw [hk]; positivity`. Use polynomial arithmetic with `only [h1, this]`.

Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`. Use polynomial arithmetic with `only [h2, hpk', ha0]`. Establish `hq2 : 5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2) ≤ 5 / 2 * X.L.a` using `by nlinarith only [hkYb]`. Establish `e4 : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y = ((5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2)) + (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2)) / (2 * (X.L.k * X.L.Y))`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e4, div_le_iff₀ (by positivity)]`. Establish `e5 : 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) * (2 * (X.L.k * X.L.Y)) = 7 * X.L.a` using `by field_simp`. Rewrite using `[e5]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSY : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) / ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) ≤ 7 / X.L.Y`.

Establish `hPp : (0 : ℝ) < ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)` using `by linarith`. Rewrite using `[div_le_div_iff₀ hYr0 (by linarith)]`. Establish `h1 : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y ≤ 7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ))`. Establish `h2` using `mul_le_mul_of_nonneg_right hSB (by linarith : (0 : ℝ) ≤ X.L.Y)`. Establish `h3` using `mul_le_mul_of_nonneg_left hYP (by norm_num : (0 : ℝ) ≤ 7)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y = (((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * X.L.Y) * ((X.S C0 CE1 CE2).P X.p ( …` using `by ring`. Establish `e2 : 7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) = (7 * ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ)) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e, e2]`.

Conclude with `le_of_mul_le_mul_right h1 hPp`. Establish `hlg1 : 1 ≤ lgA X.p X.L.a X.r` using `lgA_ge_one_facts hS.hF`. Establish `hκ : 24 * lgA X.p X.L.a X.r ≤ kapS X`. Unfold `kapS`. Establish `h1 : (2 : ℝ) ≤ (X.r : ℝ)` using `by linarith`.

Establish `h2 : (0 : ℝ) ≤ (X.s : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : (4 : ℝ) ≤ (X.r : ℝ) ^ 2` using `by nlinarith only [h1]`. Establish `h4 : (6 : ℝ) ≤ 3 * ((X.s : ℝ) + 2)` using `by linarith`. Establish `h5 : (24 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2` using `by nlinarith only [h3, h4]`. Use polynomial arithmetic with `only [h5, hlg1]`.

Conclude with `epsilon_bound_M_constant _ _ X.L.Y (kapS X) (lgA X.p X.L.a X.r) CM hCM hY hYr0 (Nat.cast_nonneg _) hSY (by linarith) (by linarith) hκ`.
-/
theorem restTMEps_of (hS : SegFacts C0 CE1 CE2 X) (hE' : (X.r : ℝ) + 1 ≤ X.L.b' → EpsFacts C0 X)
    (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM := by
  intro dl hdl a ha x hx i
  have hk : X.L.k = (X.r : ℝ) + 1 := rfl
  have hk0 : X.L.k ≠ 0 := by rw [hk]; have := r5 hS; linarith
  have hY0 : X.L.Y ≠ 0 := by have := hS.Y1; linarith
  have hr5 := r5 hS
  have hY := hS.Y1
  have hb0 := hS.hF.b0
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP : ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.b' := hS.kP _
  have hb5 : (X.r : ℝ) + 1 ≤ X.L.b' := by
    have := mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ (X.r : ℝ) + 1)
    linarith
  have hkY0 : 0 < X.L.k * X.L.Y := by rw [hk]; exact mul_pos (by linarith) (by linarith)
  have hE := hE' hb5
  have hkYb := hE.kYb
  have h4Y : 4 * X.L.Y ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; nlinarith only [hr5, hY]
  have hYb' : 4 * X.L.Y * X.L.b' ≤ X.L.a := by
    have := mul_le_mul_of_nonneg_right h4Y hb0.le
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    linarith
  have hroomR : (X.L.a : ℝ) + 2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      X.L.a + X.L.a / (X.L.k * X.L.Y) - 1 := by
    have h1 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k ≤ 3 * X.L.b' := by
      rw [hk]; nlinarith only [hkP, hb5]
    have h2 : 3 * X.L.b' * X.L.Y ≤ X.L.a := by nlinarith only [hYb', hY, hb0]
    have h3 : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) ≤ X.L.a / (X.L.k * X.L.Y) := by
      rw [le_div_iff₀ hkY0]
      have : (2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * (X.L.k * X.L.Y) =
          ((2 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) + 1) * X.L.k) * X.L.Y := by ring
      rw [this]
      nlinarith only [h1, h2, hY]
    linarith
  have hwin : (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) - 1 <
      ((⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa)
    have := hS.xa0
    linarith
  have hroom : X.L.a + 2 * (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) ≤
      ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := hS.xa0
    linarith
  have hYl := Yl_bound hS hFree hdl ha hx i hroom
  have hYP : X.L.a / (2 * (X.L.k * X.L.Y)) ≤
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    have h1 : 1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ X.L.a / (2 * (X.L.k * X.L.Y)) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1) ≤ 2 * X.L.b' := by
        nlinarith only [hkP, hb5]
      rw [hk]
      have : (1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * (2 * (((X.r : ℝ) + 1) * X.L.Y)) =
          2 * X.L.Y * ((1 + ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) * ((X.r : ℝ) + 1)) := by ring
      rw [this]
      nlinarith only [h2, hYb', hY]
    have h4 : X.L.a / (X.L.k * X.L.Y) = 2 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by field_simp
    linarith
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  have hT' := (mem_cbox' ha').1
  have hSB := S_bound hS _ hT' x.1 hK' x.2 i
  have eS : (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
      (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i =
      (gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i := by
    rw [setTies_top ha hx]
    rfl
  unfold epsM flipOneThree.InstM.eps flipOneThree.InstM.Si flipOneThree.InstM.LLt
  rw [eS]
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hp0 : (0 : ℝ) < X.p := by nlinarith only [hp, hr5]
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hB2 : 0 < X.L.a / (2 * (X.L.k * X.L.Y)) := by
    have : (0 : ℝ) < X.L.a := by nlinarith only [hYb', hY, hb0]
    positivity
  have hYr0 : (0 : ℝ) < ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) := by
    have h2 := lt_of_lt_of_le hB2 hYP
    exact pos_of_mul_pos_left h2 (by linarith)
  have hB1 : 0 ≤ 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
    have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    positivity
  have hfin : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y ≤ 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) := by
    have hq : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) ≤ 4 * X.L.a := by
      have hpk' := hE.pk
      have h1 : (2 * (X.s : ℝ) + 1) ≤ X.L.k := by rw [hk]; linarith
      have e3 : (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2) =
          4 * X.L.a * ((2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2) / X.p := by ring
      rw [e3, div_le_iff₀ hp0]
      have h2 : (2 * (X.s : ℝ) + 1) * X.L.k * X.L.Y ^ 2 ≤ X.L.k ^ 2 * X.L.Y ^ 2 := by
        have : 0 ≤ X.L.k * X.L.Y ^ 2 := by rw [hk]; positivity
        nlinarith only [h1, this]
      have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
      nlinarith only [h2, hpk', ha0]
    have hq2 : 5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2) ≤ 5 / 2 * X.L.a := by nlinarith only [hkYb]
    have e4 : (5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p)) * X.L.Y =
        ((5 / 2 * X.L.b' * (2 * X.L.k * X.L.Y ^ 2)) + (2 * (X.s : ℝ) + 1) * (2 * X.L.a / X.p) * (2 * X.L.k * X.L.Y ^ 2)) /
          (2 * (X.L.k * X.L.Y)) := by
      field_simp
    rw [e4, div_le_iff₀ (by positivity)]
    have e5 : 7 * (X.L.a / (2 * (X.L.k * X.L.Y))) * (2 * (X.L.k * X.L.Y)) = 7 * X.L.a := by field_simp
    rw [e5]
    linarith
  have hSY : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) /
      ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) ≤ 7 / X.L.Y := by
    have hPp : (0 : ℝ) < ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by linarith
    rw [div_le_div_iff₀ hYr0 (by linarith)]
    have h1 : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y ≤
        7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_right hSB (by linarith : (0 : ℝ) ≤ X.L.Y)
      have h3 := mul_le_mul_of_nonneg_left hYP (by norm_num : (0 : ℝ) ≤ 7)
      linarith
    have e : ((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) *
        ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) * X.L.Y =
        (((gT C0 CE1 CE2 X x.1).S (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2) i : ℝ) * X.L.Y) *
          ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by ring
    have e2 : 7 * (((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) =
        (7 * ((XMof C0 CE1 CE2 X dl a x.1 x.2).Yl i : ℝ)) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      ring
    rw [e, e2] at h1
    exact le_of_mul_le_mul_right h1 hPp
  have hlg1 : 1 ≤ lgA X.p X.L.a X.r := lgA_ge_one_facts hS.hF
  have hκ : 24 * lgA X.p X.L.a X.r ≤ kapS X := by
    unfold kapS
    have h1 : (2 : ℝ) ≤ (X.r : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
    have h3 : (4 : ℝ) ≤ (X.r : ℝ) ^ 2 := by nlinarith only [h1]
    have h4 : (6 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) := by linarith
    have h5 : (24 : ℝ) ≤ 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 := by nlinarith only [h3, h4]
    nlinarith only [h5, hlg1]
  exact epsilon_bound_M_constant _ _ X.L.Y (kapS X) (lgA X.p X.L.a X.r) CM hCM hY hYr0 (Nat.cast_nonneg _) hSY (by linarith) (by linarith) hκ

/- English proof (translation)
The claim follows from `restTMEps_of hS (epsFacts hCYb hC0 hH hS) hFree CM hCM`.
-/
theorem restTMEps_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hC0 : 1 ≤ C0) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (CM : ℝ) (hCM : 1 ≤ CM) : RestTMEps C0 CE1 CE2 X CM :=
  restTMEps_of hS (epsFacts hCYb hC0 hH hS) hFree CM hCM

/- English proof (translation)
Take `⟨CM, hCM, h⟩` from `restTM_exists`. Use `⟨CM, hCM, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hYb hCb hCD hC0 hE1 hE2 hH => ?_⟩` and prove the remaining obligations. Establish `hS` using `segFacts hYb hCb hCD hE1 hE2 hH (CE1 := CE1) (CE2 := CE2)`. Establish `hF` using `restFree_proved hS`. Conclude with `h D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF (restTMSize_proved hS hF) (restTMEps_proved hYb hC0 hH hS hF CM hCM)`.
-/
theorem restTM_closed : ∃ CM : ℝ, 1 ≤ CM ∧ ∀ (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 CYb Cde Ck CD Cb Cc : ℝ) (X : flipOneThree.Inst),
    2 ≤ CYb → 1 ≤ Cb → 0 ≤ CD → 1 ≤ C0 → 0 ≤ CE1 → 0 ≤ CE2 →
      flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestTM C0 CE1 CE2 X CM := by
  obtain ⟨CM, hCM, h⟩ := restTM_exists
  refine ⟨CM, hCM, fun D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hYb hCb hCD hC0 hE1 hE2 hH => ?_⟩
  have hS := segFacts hYb hCb hCD hE1 hE2 hH (CE1 := CE1) (CE2 := CE2)
  have hF := restFree_proved hS
  exact h D C0 CE1 CE2 CYb Cde Ck CD Cb Cc X hH hF (restTMSize_proved hS hF)
    (restTMEps_proved hYb hC0 hH hS hF CM hCM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
