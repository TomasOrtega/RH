import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.RBLam

open Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

/- English proof (translation)
Establish `hx1 : 1 ≤ L.sc.x` using `le_of_lt L.sc.one_lt_alt`. Establish `hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps` using `Real.one_le_rpow hx1 L.sc.eps_pos.le`. Establish `hX0 : (0 : ℝ) ≤ L.sc.x ^ L.sc.eps` using `by linarith`. Establish `hg0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `hlam : Real.log (Fintype.card G : ℝ) ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ))`.

Establish `h` using `GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)`. Rewrite using `[hc]`. Conclude with `h`. Establish `hth : L.sc.x ^ szTh L ≤ L.sc.x ^ L.sc.eps`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises.

Unfold `szTh`. Combine the linear relations using `[L.sc.eps_pos]`. Establish `hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps)`. Rewrite using `[Real.log_mul (by norm_num) hg0.ne']`. Establish `h1` using `(hSG 0 0).2.2`.

Establish `h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps` using `by show L.sc.x ^ szTh L * L.sc.x ^ L.sc.eps ≤ _`. Conclude with `mul_le_mul_of_nonneg_right hth hX0`. Establish `h3` using `Real.log_two_lt_d9`. Establish `h4 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hr` using `two_r_sq_le_b L hSC`. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 2` using `pow_nonneg (Nat.cast_nonneg _) 2`. Establish `hb0 : (0 : ℝ) ≤ L.sc.b` using `by linarith`.

Use `set X := L.sc.x ^ L.sc.eps with hXdef`. Establish `hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)` using `rfl`. Rewrite using `[hU]`. Establish `hXX : (0 : ℝ) ≤ X * X` using `mul_nonneg hX0 hX0`. Establish `h2XX : (0 : ℝ) ≤ 2 * (X * X)` using `by positivity`.

Establish `hbm : L.sc.b ≤ (D.R.m : ℝ) * L.sc.b` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Use `hlam.trans (mul_le_mul_of_nonneg_left hlg ?_)` and prove the remaining obligations. Check the signs of the components of the expression. Use `_ = (D.R.f : ℝ) * (2 * (D.R.r : ℝ) ^ 2) * (2 * (X * X)) := by ring`.

Use `_ ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) * L.sc.b) * (2 * (X * X)) := by`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hr.trans hbm) hf0) h2XX`. Use `_ = 2 * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + 0)) := by ring`. Use `_ ≤ 2 * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)) := by gcongr`.
-/
theorem log_card_le_unit_exponent {G : Type} [Fintype G] (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L) (Del h0 : ℕ) (Nc : ℝ)
    (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) :
    Real.log (Fintype.card G : ℝ) ≤ 2 * (ofRecord D L Del h0).unitE Nc := by
  have hx1 : 1 ≤ L.sc.x := le_of_lt L.sc.one_lt_alt
  have hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hX0 : (0 : ℝ) ≤ L.sc.x ^ L.sc.eps := by linarith
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hlam : Real.log (Fintype.card G : ℝ) ≤
      2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := by
    have h := GZeroLogBound D (D.host.g 0 : ℝ) (fun i => (hSG i 0).2.1)
    rw [hc]
    exact h
  have hth : L.sc.x ^ szTh L ≤ L.sc.x ^ L.sc.eps := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlg : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 2 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h1 := (hSG 0 0).2.2
    have h2 : L.sc.x ^ szTh L * L.sc.L ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
      show L.sc.x ^ szTh L * L.sc.x ^ L.sc.eps ≤ _
      exact mul_le_mul_of_nonneg_right hth hX0
    have h3 := Real.log_two_lt_d9
    have h4 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by nlinarith
    linarith
  have hr := two_r_sq_le_b L hSC
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := pow_nonneg (Nat.cast_nonneg _) 2
  have hb0 : (0 : ℝ) ≤ L.sc.b := by linarith
  set X := L.sc.x ^ L.sc.eps with hXdef
  have hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) := rfl
  rw [hU]
  have hXX : (0 : ℝ) ≤ X * X := mul_nonneg hX0 hX0
  have h2XX : (0 : ℝ) ≤ 2 * (X * X) := by positivity
  have hbm : L.sc.b ≤ (D.R.m : ℝ) * L.sc.b := by nlinarith
  calc Real.log (Fintype.card G : ℝ)
      ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (2 * (X * X)) := by
        refine hlam.trans (mul_le_mul_of_nonneg_left hlg ?_)
        positivity
    _ = (D.R.f : ℝ) * (2 * (D.R.r : ℝ) ^ 2) * (2 * (X * X)) := by ring
    _ ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) * L.sc.b) * (2 * (X * X)) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hr.trans hbm) hf0) h2XX
    _ = 2 * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + 0)) := by ring
    _ ≤ 2 * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)) := by gcongr

/- English proof (translation)
Establish `hN : D.host.QS * D.host.q * D.host.d ≠ 0` using `Nat.mul_ne_zero (Nat.mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero`. Use `haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN⟩`. Establish `h1 : Nat.card D.R.toFrame.GG ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ` using `Nat.card_le_card_of_surjective _ D.host.der.art_surj`. Establish `h2 : Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))` using `Nat.card_le_card_of_injective _ Units.val_injective`. Rewrite `h2` using `[Nat.card_zmod]`.

Rewrite `h1` using `[D.R.toFrame.natCard_GG]`. Conclude with `h1.trans h2`.
-/
private theorem four_n_le_cond (D : D7) : 4 * D.R.n ≤ D.host.QS * D.host.q * D.host.d := by
  have hN : D.host.QS * D.host.q * D.host.d ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero
  haveI : NeZero (D.host.QS * D.host.q * D.host.d) := ⟨hN⟩
  have h1 : Nat.card D.R.toFrame.GG ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ :=
    Nat.card_le_card_of_surjective _ D.host.der.art_surj
  have h2 : Nat.card (ZMod (D.host.QS * D.host.q * D.host.d))ˣ ≤ Nat.card (ZMod (D.host.QS * D.host.q * D.host.d)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  rw [Nat.card_zmod] at h2
  rw [D.R.toFrame.natCard_GG] at h1
  exact h1.trans h2

/- English proof (translation)
Establish `h` using `hF u`. Establish `hx1 : 1 ≤ L.sc.x` using `le_of_lt L.sc.one_lt_alt`. Establish `hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps` using `Real.one_le_rpow hx1 L.sc.eps_pos.le`. Establish `hq : (1 : ℝ) ≤ D.host.q` using `by exact_mod_cast D.host.hyp.1.one_lt.le`. Establish `hd : (1 : ℝ) ≤ D.host.d` using `by exact_mod_cast D.host.hyp.2.1.one_lt.le`.

Establish `hn : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `hnq : (1 : ℝ) ≤ (D.R.n : ℝ) * D.host.q` using `by nlinarith`. Establish `h4c : 4 * (D.R.n : ℝ) ≤ szCond L`.

Establish `h4 : ((4 * D.R.n : ℕ) : ℝ) ≤ ((D.host.QS * D.host.q * D.host.d : ℕ) : ℝ)` using `Nat.cast_le.2 (four_n_le_cond D)`. Move the coercions through the operations in `at h4`. Conclude with `h4`. Establish `hc1 : (1 : ℝ) ≤ szCond L` using `by linarith`. Establish `hfc : (D.R.f : ℝ) ≤ szCond L`.

Unfold `Ranks.f`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkt : D.R.k + D.R.m + 4 ≤ D.R.t`. Use `D.R.rank_add_five_le` as an intermediate fact.

Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h2m` using `D.R.two_le_m`. Establish `ht5 : (5 : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : 5 ≤ D.R.t)`. Establish `hk : (D.R.k : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.k ≤ D.R.t)`.

Establish `hm : (D.R.m : ℝ) ≤ D.R.t` using `by exact_mod_cast (by omega : D.R.m ≤ D.R.t)`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hN : (D.R.N D.R.m : ℝ) ≤ 3 * (D.R.t : ℝ) ^ 2`. Unfold `Ranks.N`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hN1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Establish `: 1 ≤ D.R.N D.R.m` using `by unfold Ranks.N; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ D.R.f`.

Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f; have : 1 ≤ D.R.n := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `by linarith`. Establish `h36 : szCond L ≤ szCond L ^ 36` using `le_self_pow₀ hc1 (by norm_num)`. Establish `ht150 : (D.R.t : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 150` using `pow_le_pow_right₀ (by linarith) (by norm_num)`.

Establish `hSC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b` using `hSC`. Use `set a : ℝ := (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) with ha`. Establish `ha1 : (1 : ℝ) ≤ a` using `by nlinarith`. Establish `hab : a ≤ 3 * Real.sqrt L.sc.b`. Establish `e1 : a ≤ szCond L ^ 36 * (3 * (D.R.t : ℝ) ^ 150)`.

Establish `h1 : (D.R.N D.R.m : ℝ) ≤ 3 * (D.R.t : ℝ) ^ 150` using `by linarith`. Establish `h2 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Establish `hb1 : (1 : ℝ) ≤ L.sc.b`.

Unfold `Scale.b`. Conclude with `Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith) _)`. Establish `hsb : Real.sqrt L.sc.b ≤ L.sc.b`. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Use `set X := L.sc.x ^ L.sc.eps with hXdef`. Establish `hlogb : Real.log L.sc.b = X`. Unfold `Scale.b Scale.L`. Rewrite using `[Real.log_exp]`. Establish `hloga : Real.log a ≤ 3 * X`.

Establish `hs0 : 0 < Real.sqrt L.sc.b` using `Real.sqrt_pos.2 (by linarith)`. Establish `e1 : Real.log a ≤ Real.log (3 * Real.sqrt L.sc.b)` using `Real.log_le_log (by linarith) hab`. Rewrite `e1` using `[Real.log_mul (by norm_num) hs0.ne', Real.log_sqrt (by linarith), hlogb]`. Establish `e2 : Real.log 3 ≤ 3 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hla0 : (0 : ℝ) ≤ Real.log a` using `Real.log_nonneg ha1`. Establish `hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)` using `rfl`. Rewrite using `[hU]`. Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hX0 : (0 : ℝ) ≤ X` using `by linarith`.

Establish `hkey : a * Real.log a ≤ 9 * (L.sc.b * X)`. Establish `e1 : a * Real.log a ≤ (3 * Real.sqrt L.sc.b) * (3 * X)` using `mul_le_mul hab hloga hla0 (by positivity)`. Establish `e2 : Real.sqrt L.sc.b * X ≤ L.sc.b * X` using `mul_le_mul_of_nonneg_right hsb hX0`. Establish `e3 : (3 * Real.sqrt L.sc.b) * (3 * X) = 9 * (Real.sqrt L.sc.b * X)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbX : L.sc.b * X ≤ X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)`. Establish `hfm : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m` using `one_le_mul_of_one_le_of_one_le hf1 hm1`. Establish `hfmX : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m * X` using `one_le_mul_of_one_le_of_one_le hfm hX1`. Establish `hb0 : (0 : ℝ) ≤ L.sc.b` using `by linarith`. Establish `e1 : L.sc.b * 1 ≤ L.sc.b * ((D.R.f : ℝ) * D.R.m * X)` using `mul_le_mul_of_nonneg_left hfmX hb0`.

Establish `e2 : L.sc.b * X ≤ ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X`. Use `mul_le_mul_of_nonneg_right e1 hX0` as an intermediate fact. Establish `e3 : L.sc.b * ((D.R.f : ℝ) * D.R.m * X) * X = ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : (0 : ℝ) ≤ X * Nc` using `mul_nonneg hX0 hNc`.

Establish `e5 : X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) = ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X + X * Nc` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : Real.log ((D.mem u).C.DGam : ℝ) ≤ C * (a * Real.log a)`. Establish `: C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) = C * (a * Real.log a)`. Rewrite using `[ha]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear relations using `[h, this.le, this.ge]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_DGam_le (L : SizeData₂ D) (hSC : SizeCond L) (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) (u : D.what₂.Word)
    (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) :
    Real.log ((D.mem u).C.DGam : ℝ) ≤ 9 * C * (ofRecord D L Del h0).unitE Nc := by
  have h := hF u
  have hx1 : 1 ≤ L.sc.x := le_of_lt L.sc.one_lt_alt
  have hX1 : (1 : ℝ) ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hnq : (1 : ℝ) ≤ (D.R.n : ℝ) * D.host.q := by nlinarith
  have h4c : 4 * (D.R.n : ℝ) ≤ szCond L := by
    have h4 : ((4 * D.R.n : ℕ) : ℝ) ≤ ((D.host.QS * D.host.q * D.host.d : ℕ) : ℝ) :=
      Nat.cast_le.2 (four_n_le_cond D)
    push_cast at h4
    exact h4
  have hc1 : (1 : ℝ) ≤ szCond L := by linarith
  have hfc : (D.R.f : ℝ) ≤ szCond L := by
    unfold Ranks.f
    push_cast
    linarith
  have hkt : D.R.k + D.R.m + 4 ≤ D.R.t := by
    have := D.R.rank_add_five_le
    have := D.R.two_le_m
    omega
  have h2m := D.R.two_le_m
  have ht5 : (5 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 5 ≤ D.R.t)
  have hk : (D.R.k : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.k ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN : (D.R.N D.R.m : ℝ) ≤ 3 * (D.R.t : ℝ) ^ 2 := by
    unfold Ranks.N
    push_cast
    nlinarith
  have hN1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f; have : 1 ≤ D.R.n := D.R.ord_pos; omega
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ D.R.t := by linarith
  have h36 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have ht150 : (D.R.t : ℝ) ^ 2 ≤ (D.R.t : ℝ) ^ 150 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hSC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hSC
  set a : ℝ := (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) with ha
  have ha1 : (1 : ℝ) ≤ a := by nlinarith
  have hab : a ≤ 3 * Real.sqrt L.sc.b := by
    have e1 : a ≤ szCond L ^ 36 * (3 * (D.R.t : ℝ) ^ 150) := by
      have h1 : (D.R.N D.R.m : ℝ) ≤ 3 * (D.R.t : ℝ) ^ 150 := by linarith
      have h2 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by linarith
      calc a = (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) := rfl
        _ ≤ szCond L ^ 36 * (3 * (D.R.t : ℝ) ^ 150) :=
          mul_le_mul (hfc.trans h36) h1 h2 (by positivity)
    nlinarith
  have hb1 : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith) _)
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  set X := L.sc.x ^ L.sc.eps with hXdef
  have hlogb : Real.log L.sc.b = X := by
    unfold Scale.b Scale.L
    rw [Real.log_exp]
  have hloga : Real.log a ≤ 3 * X := by
    have hs0 : 0 < Real.sqrt L.sc.b := Real.sqrt_pos.2 (by linarith)
    have e1 : Real.log a ≤ Real.log (3 * Real.sqrt L.sc.b) := Real.log_le_log (by linarith) hab
    rw [Real.log_mul (by norm_num) hs0.ne', Real.log_sqrt (by linarith), hlogb] at e1
    have e2 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hla0 : (0 : ℝ) ≤ Real.log a := Real.log_nonneg ha1
  have hU : (ofRecord D L Del h0).unitE Nc = X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) := rfl
  rw [hU]
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hkey : a * Real.log a ≤ 9 * (L.sc.b * X) := by
    have e1 : a * Real.log a ≤ (3 * Real.sqrt L.sc.b) * (3 * X) :=
      mul_le_mul hab hloga hla0 (by positivity)
    have e2 : Real.sqrt L.sc.b * X ≤ L.sc.b * X := mul_le_mul_of_nonneg_right hsb hX0
    have e3 : (3 * Real.sqrt L.sc.b) * (3 * X) = 9 * (Real.sqrt L.sc.b * X) := by ring
    linarith
  have hbX : L.sc.b * X ≤ X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) := by
    have hfm : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m := one_le_mul_of_one_le_of_one_le hf1 hm1
    have hfmX : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m * X := one_le_mul_of_one_le_of_one_le hfm hX1
    have hb0 : (0 : ℝ) ≤ L.sc.b := by linarith
    have e1 : L.sc.b * 1 ≤ L.sc.b * ((D.R.f : ℝ) * D.R.m * X) := mul_le_mul_of_nonneg_left hfmX hb0
    have e2 : L.sc.b * X ≤ ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X := by
      have := mul_le_mul_of_nonneg_right e1 hX0
      have e3 : L.sc.b * ((D.R.f : ℝ) * D.R.m * X) * X = ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X := by ring
      linarith
    have e4 : (0 : ℝ) ≤ X * Nc := mul_nonneg hX0 hNc
    have e5 : X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc) = ((D.R.f : ℝ) * D.R.m * L.sc.b * X) * X + X * Nc := by ring
    linarith
  have hh : Real.log ((D.mem u).C.DGam : ℝ) ≤ C * (a * Real.log a) := by
    have : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) = C * (a * Real.log a) := by
      rw [ha]; ring
    linarith [h, this.le, this.ge]
  calc Real.log ((D.mem u).C.DGam : ℝ) ≤ C * (a * Real.log a) := hh
    _ ≤ C * (9 * (L.sc.b * X)) := mul_le_mul_of_nonneg_left hkey hC
    _ ≤ C * (9 * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc))) := by gcongr
    _ = 9 * C * (X * ((D.R.f : ℝ) * D.R.m * L.sc.b * X + Nc)) := by ring

/- English proof (translation)
Unfold `DGamSize`. Establish `hdvd : dgOf A P0 ψ0 hT ∣ Fintype.card G * (D.mem u0).C.DGam`. Unfold `dgOf`. Apply `Finset.lcm_dvd` to reduce the goal to its premises. Introduce `p _`.

Unfold `BlockDat.DG`. Apply `Nat.mul_dvd_mul` to reduce the goal to its premises. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `Subgroup.card_subgroup_dvd_card _`. Unfold `CSD.DGam`.

Conclude with `Finset.lcm_dvd fun c _ => hGam p.1 p.2 c`. Establish `hG : 0 < Fintype.card G` using `Fintype.card_pos`. Establish `hD : 0 < (D.mem u0).C.DGam` using `(D.mem u0).C.DGam_pos`. Establish `hpos : 0 < Fintype.card G * (D.mem u0).C.DGam` using `Nat.mul_pos hG hD`. Establish `hle : (dgOf A P0 ψ0 hT : ℝ) ≤ (Fintype.card G : ℝ) * ((D.mem u0).C.DGam : ℝ)`.

Conclude with `Nat.le_of_dvd hpos hdvd` after adjusting the coercions. Establish `hdg : (0 : ℝ) < (dgOf A P0 ψ0 hT : ℝ)` using `by exact_mod_cast dgOf_pos A P0 ψ0 hT`. Establish `hlog : Real.log (dgOf A P0 ψ0 hT : ℝ) ≤ Real.log (Fintype.card G : ℝ) + Real.log ((D.mem u0).C.DGam : ℝ)`. Rewrite using `[← Real.log_mul (by exact_mod_cast hG.ne') (by exact_mod_cast hD.ne')]`. Conclude with `Real.log_le_log hdg hle`.

Establish `h1` using `log_card_le_unit_exponent (G := G) L hSG hSC Del h0 Nc hNc hc`. Establish `h2` using `log_DGam_le L hSC C hC hF u0 Del h0 Nc hNc`. Establish `e : (2 + 9 * C + cs) * (ofRecord D L Del h0).unitE Nc = 2 * (ofRecord D L Del h0).unitE Nc + 9 * C * (ofRecord D L Del h0).unitE Nc + cs * (ofRecord D L Del h0).unitE Nc`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dGamSize_record {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (hT : Finite T) (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L)
    (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (u0 : D.what₂.Word)
    (hGam : ∀ j t c, Fintype.card ((A.fam.L j t).S.Gam c) ∣ (D.mem u0).C.DGam)
    (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) (s : ℕ) (cs : ℝ)
    (hs : Real.log (s : ℝ) ≤ cs * (ofRecord D L Del h0).unitE Nc) :
    DGamSize A P0 ψ0 (ofRecord D L Del h0) Nc hT s (2 + 9 * C + cs) := by
  unfold DGamSize
  have hdvd : dgOf A P0 ψ0 hT ∣ Fintype.card G * (D.mem u0).C.DGam := by
    unfold dgOf
    apply Finset.lcm_dvd
    intro p _
    unfold BlockDat.DG
    apply Nat.mul_dvd_mul
    · rw [← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card _
    · unfold CSD.DGam
      exact Finset.lcm_dvd fun c _ => hGam p.1 p.2 c
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have hD : 0 < (D.mem u0).C.DGam := (D.mem u0).C.DGam_pos
  have hpos : 0 < Fintype.card G * (D.mem u0).C.DGam := Nat.mul_pos hG hD
  have hle : (dgOf A P0 ψ0 hT : ℝ) ≤ (Fintype.card G : ℝ) * ((D.mem u0).C.DGam : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos hdvd
  have hdg : (0 : ℝ) < (dgOf A P0 ψ0 hT : ℝ) := by exact_mod_cast dgOf_pos A P0 ψ0 hT
  have hlog : Real.log (dgOf A P0 ψ0 hT : ℝ) ≤ Real.log (Fintype.card G : ℝ) + Real.log ((D.mem u0).C.DGam : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hG.ne') (by exact_mod_cast hD.ne')]
    exact Real.log_le_log hdg hle
  have h1 := log_card_le_unit_exponent (G := G) L hSG hSC Del h0 Nc hNc hc
  have h2 := log_DGam_le L hSC C hC hF u0 Del h0 Nc hNc
  have e : (2 + 9 * C + cs) * (ofRecord D L Del h0).unitE Nc =
      2 * (ofRecord D L Del h0).unitE Nc + 9 * C * (ofRecord D L Del h0).unitE Nc + cs * (ofRecord D L Del h0).unitE Nc := by
    ring
  rw [e]
  linarith

/- English proof (translation)
Establish `h` using `dGamSize_record A P0 ψ0 hT L hSG hSC Del h0 Nc hNc hc u0 hGam C hC hF 1 0 (by simp)`. Rewrite `h` using `[add_zero]`. Conclude with `h`.
-/
theorem dGamSize_record_one {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (hT : Finite T) (L : SizeData₂ D) (hSG : SizeG L) (hSC : SizeCond L)
    (Del h0 : ℕ) (Nc : ℝ) (hNc : 0 ≤ Nc) (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (u0 : D.what₂.Word)
    (hGam : ∀ j t c, Fintype.card ((A.fam.L j t).S.Gam c) ∣ (D.mem u0).C.DGam)
    (C : ℝ) (hC : 0 ≤ C) (hF : FactDGam D C) :
    DGamSize A P0 ψ0 (ofRecord D L Del h0) Nc hT 1 (2 + 9 * C) := by
  have h := dGamSize_record A P0 ψ0 hT L hSG hSC Del h0 Nc hNc hc u0 hGam C hC hF 1 0 (by simp)
  rw [add_zero] at h
  exact h

end Formalism.L2.DIV.Cons

end
