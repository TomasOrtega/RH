import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory.Alc

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Establish `h : ((((D.fm u).lam i τ).w a : ℤ) : ℚ) = flipTwoThree.lamLiftN D u τ a.1`. Rewrite using `[(D.fm u).lam_eq i hi τ a]`. Unfold `flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ`. Distinguish the cases in `h : a.1 < D.R.k`. Rewrite using `[dif_pos h, if_pos h, dif_pos h]`.

Rewrite using `[dif_neg h, if_neg h, dif_pos (D.R.blk_lt hi a h)]`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem entryR (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N i)) :
    ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = ((flipTwoThree.lamLiftN D u τ a.1 : ℚ) : ℝ) := by
  have h : ((((D.fm u).lam i τ).w a : ℤ) : ℚ) = flipTwoThree.lamLiftN D u τ a.1 := by
    rw [(D.fm u).lam_eq i hi τ a]
    unfold flipTwoThree.lamLiftN flipTwoThree.lamCol flipTwoThree.wJ
    by_cases h : a.1 < D.R.k
    · rw [dif_pos h, if_pos h, dif_pos h]
    · rw [dif_neg h, if_neg h, dif_pos (D.R.blk_lt hi a h)]
  rw [← h]
  simp

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => exact le_rfl`. Consider the case `succ n ih => exact le_trans (ih (by omega)) (h n hc)`.
-/
theorem wJ_mono {D : D7} {u : D.what₂.Word} {τ : D.what₂.Tau}
    (h : ∀ j, j + 1 < D.R.m → flipTwoThree.wJ D u τ j ≤ flipTwoThree.wJ D u τ (j + 1)) (c : ℕ) (hc : c < D.R.m) :
    flipTwoThree.wJ D u τ 0 ≤ flipTwoThree.wJ D u τ c := by
  induction c with
  | zero => exact le_rfl
  | succ n ih => exact le_trans (ih (by omega)) (h n hc)

/- English proof (translation)
Take `⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, n16⟩` from `hN u`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hNn : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`.

Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `ht : (11 : ℝ) ≤ D.R.t`. Establish `h1` using `D.R.rank_add_five_le`. Establish `h2` using `D.R.m_add_three_le_k`. Establish `h3` using `D.R.two_le_m`.

Establish `: 11 ≤ D.R.t` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hmt : (22 : ℝ) ≤ D.R.m * D.R.t` using `by nlinarith`. Establish `hq : 24 ≤ L.sc.b' / L.sc.x` using `by linarith`. Establish `hb24 : 24 * L.sc.x ≤ L.sc.b'` using `by rwa [le_div_iff₀ hx0] at hq`.

Establish `hb0 : 0 < L.sc.b'` using `by nlinarith`. Establish `hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 2` using `div_le_div_of_nonneg_left hb0.le (by norm_num) n14`. Establish `hbb : L.sc.b' ≤ L.sc.b`. Rewrite `n6` using `[mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne']`. Then use the resulting hypothesis. Establish `hNb : (D.R.N D.R.m : ℝ) ≤ L.sc.b'`.

Establish `h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L)` using `mul_le_mul_of_nonneg_left (by nlinarith) hNn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN1 : (1 : ℝ) ≤ D.R.N D.R.m` using `by exact_mod_cast D.R.N_pos D.R.m`. Establish `hm3 : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3` using `by nlinarith [mul_self_nonneg ((D.R.m : ℝ) - 2)]`. Establish `hmN : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 * D.R.N D.R.m` using `by nlinarith`.

Use `⟨hb24, hbb, hNb, by linarith, by linarith, n7, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hC : Cn ≤ 0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC' : 0 < Cn` using `not_le.1 hC`. Establish `h2 : (1 + 2 * (2 * Cn + 4)) * 8 ≤ (1 + 2 * (2 * Cn + 4)) * ((D.R.m : ℝ) ^ 3 * D.R.N D.R.m)` using `mul_le_mul_of_nonneg_left hmN (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nums {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (u : D.what₂.Word) (hN : J.NumsL D L Cn cL) :
    24 * L.sc.x ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.b' ∧ 2 * L.Sc ≤ L.sc.b' ∧ 2 * L.etaSz ≤ L.sc.b' ∧
      1 ≤ L.Sc ∧ 32 * Cn ≤ L.sc.b' := by
  obtain ⟨n1, _, _, _, _, n6, n7, n8, n9, _, n11, _, _, n14, _, n16⟩ := hN u
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNn : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (11 : ℝ) ≤ D.R.t := by
    have h1 := D.R.rank_add_five_le
    have h2 := D.R.m_add_three_le_k
    have h3 := D.R.two_le_m
    have : 11 ≤ D.R.t := by omega
    exact_mod_cast this
  have hmt : (22 : ℝ) ≤ D.R.m * D.R.t := by nlinarith
  have hq : 24 ≤ L.sc.b' / L.sc.x := by linarith
  have hb24 : 24 * L.sc.x ≤ L.sc.b' := by rwa [le_div_iff₀ hx0] at hq
  have hb0 : 0 < L.sc.b' := by nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb0.le (by norm_num) n14
  have hbb : L.sc.b' ≤ L.sc.b := by
    rwa [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hx0.ne'] at n6
  have hNb : (D.R.N D.R.m : ℝ) ≤ L.sc.b' := by
    have h1 : (D.R.N D.R.m : ℝ) * 1 ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hNn
    linarith
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast D.R.N_pos D.R.m
  have hm3 : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith [mul_self_nonneg ((D.R.m : ℝ) - 2)]
  have hmN : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 * D.R.N D.R.m := by nlinarith
  refine ⟨hb24, hbb, hNb, by linarith, by linarith, n7, ?_⟩
  by_cases hC : Cn ≤ 0
  · linarith
  · have hC' : 0 < Cn := not_le.1 hC
    have h2 : (1 + 2 * (2 * Cn + 4)) * 8 ≤ (1 + 2 * (2 * Cn + 4)) * ((D.R.m : ℝ) ^ 3 * D.R.N D.R.m) :=
      mul_le_mul_of_nonneg_left hmN (by linarith)
    nlinarith

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `nums hcL u hN`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hb0 : 0 < L.sc.b'` using `by linarith`. Establish `hxb : 0 ≤ L.sc.x * L.sc.b` using `mul_nonneg (by linarith) (by linarith)`. Establish `hsq : 0 ≤ L.sc.b' * L.sc.b' / 64` using `by positivity`.

Establish `hxb1 : L.sc.b ≤ L.sc.x * L.sc.b` using `le_mul_of_one_le_left (by linarith) hx1.le`. Establish `hCS : Cn * L.Sc ≤ L.sc.b' * L.sc.b' / 64`. Distinguish the cases in `hC : Cn ≤ 0`. Establish `: Cn * L.Sc ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hC (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC' : 0 < Cn` using `not_le.1 hC`. Establish `: (32 * Cn) * (2 * L.Sc) ≤ L.sc.b' * L.sc.b'` using `mul_le_mul s7 s4 (by linarith) hb0.le`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨_, w2, w3, w4, w5, w6, w7, _⟩` from `hW u τ`. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `w7' : -((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ)` using `by exact_mod_cast w7`. Establish `hlast : ((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ L.sc.b' * L.sc.b' / 64`. Distinguish the cases in `hT : flipTwoThree.IsTop D τ`. Use `(w2 hT).2.2.1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(w3 hT (D.R.k - 1) (by omega)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[entryR D u i hi τ a]`. Unfold `flipTwoThree.lamLiftN`. Distinguish the cases in `hak : a.1 < D.R.k`.

Rewrite using `[if_pos hak]`. Distinguish the cases in `hT : flipTwoThree.IsTop D τ`. Take `⟨t1, t2, t3, t4, t5⟩` from `w2 hT`. Distinguish the cases in `h0 : a.1 = 0`. Apply the tactic sequence `rw [h0]; constructor <;> linarith`.

Distinguish the cases in `hl : a.1 < D.R.k - 1`. Take `⟨e1, e2⟩` from `t5 a.1 (Nat.pos_of_ne_zero h0) hl`. Apply the tactic sequence `constructor <;> linarith`. Establish `: a.1 = D.R.k - 1` using `by omega`. Rewrite using `[this]`.

Apply the tactic sequence `constructor <;> linarith`. Take `⟨e1, e2⟩` from `w3 hT a.1 hak`. Apply the tactic sequence `constructor <;> linarith`. Rewrite using `[if_neg hak]`. Establish `hb` using `D.R.blk_lt hi a hak`.

Establish `e2 : ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ)`. Conclude with `wJ_mono w4 _ hb` after adjusting the coercions. Establish `e1 : ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) ≤ 2 * L.sc.b + L.sc.b'`. Distinguish the cases in `hK : flipTwoThree.IsThick D τ`. Use `(w6 hK _ hb).2` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `w5 hK _ hb` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem entry_bd {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : J.NumsL D L Cn cL) (hW : J.WtsL D L Cn)
    (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i ≤ D.R.m) (a : Fin (D.R.N i)) :
    -(2 * L.sc.b + L.sc.b') ≤ ((((D.fm u).lam i τ).w a : ℤ) : ℝ) ∧
      ((((D.fm u).lam i τ).w a : ℤ) : ℝ) ≤ 2 * (L.sc.x * L.sc.b) + L.sc.b' * L.sc.b' / 64 := by
  classical
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := nums hcL u hN
  have hx1 := L.sc.one_lt_alt
  have hb0 : 0 < L.sc.b' := by linarith
  have hxb : 0 ≤ L.sc.x * L.sc.b := mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ L.sc.b' * L.sc.b' / 64 := by positivity
  have hxb1 : L.sc.b ≤ L.sc.x * L.sc.b := le_mul_of_one_le_left (by linarith) hx1.le

  have hCS : Cn * L.Sc ≤ L.sc.b' * L.sc.b' / 64 := by
    by_cases hC : Cn ≤ 0
    · have : Cn * L.Sc ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by linarith)
      linarith
    · have hC' : 0 < Cn := not_le.1 hC
      have : (32 * Cn) * (2 * L.Sc) ≤ L.sc.b' * L.sc.b' := mul_le_mul s7 s4 (by linarith) hb0.le
      linarith
  obtain ⟨_, w2, w3, w4, w5, w6, w7, _⟩ := hW u τ
  have hk := D.R.m_add_three_le_k
  have w7' : -((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ) := by exact_mod_cast w7

  have hlast : ((flipTwoThree.lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ L.sc.b' * L.sc.b' / 64 := by
    by_cases hT : flipTwoThree.IsTop D τ
    · have := (w2 hT).2.2.1
      linarith
    · have := (w3 hT (D.R.k - 1) (by omega)).2
      linarith
  rw [entryR D u i hi τ a]
  unfold flipTwoThree.lamLiftN
  by_cases hak : a.1 < D.R.k
  · rw [if_pos hak]
    by_cases hT : flipTwoThree.IsTop D τ
    · obtain ⟨t1, t2, t3, t4, t5⟩ := w2 hT
      by_cases h0 : a.1 = 0
      · rw [h0]; constructor <;> linarith
      · by_cases hl : a.1 < D.R.k - 1
        · obtain ⟨e1, e2⟩ := t5 a.1 (Nat.pos_of_ne_zero h0) hl
          constructor <;> linarith
        · have : a.1 = D.R.k - 1 := by omega
          rw [this]
          constructor <;> linarith
    · obtain ⟨e1, e2⟩ := w3 hT a.1 hak
      constructor <;> linarith
  · rw [if_neg hak]
    have hb := D.R.blk_lt hi a hak
    have e2 : ((flipTwoThree.wJ D u τ 0 : ℚ) : ℝ) ≤ ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) := by
      exact_mod_cast wJ_mono w4 _ hb
    have e1 : ((flipTwoThree.wJ D u τ ((a.1 - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) ≤ 2 * L.sc.b + L.sc.b' := by
      by_cases hK : flipTwoThree.IsThick D τ
      · have := (w6 hK _ hb).2
        linarith
      · have := w5 hK _ hb
        linarith
    push_cast
    constructor <;> linarith

/- English proof (translation)
Introduce `j hj τ a b`. Take `⟨s1, s2, s3, _, _, _, _⟩` from `nums hcL u hN`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hb24 : 24 ≤ L.sc.b` using `by linarith`. Establish `hb1 : 1 ≤ L.sc.b` using `by linarith`.

Establish `hb'0 : 0 ≤ L.sc.b'` using `by linarith`. Establish `hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ)`. Use `le_trans ?_ (hT u)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`. Use `Real.rpow_le_rpow_of_exponent_le hb1 ?_` and prove the remaining obligations.

Establish `: (4 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b` using `sq _`. Establish `h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b` using `mul_le_mul_of_nonneg_right hb24 (by linarith)`.

Establish `h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b` using `mul_le_mul_of_nonneg_right (s1.trans s2) (by linarith)`. Establish `hq : L.sc.b' * L.sc.b' ≤ L.sc.b * L.sc.b` using `mul_le_mul s2 s2 hb'0 (by linarith)`. Establish `hNj : (D.R.N j : ℝ) ≤ D.R.N D.R.m`. Establish `: D.R.N j ≤ D.R.N D.R.m`. Use `Nat.mul_le_mul_right (D.R.t + 1) hj` as an intermediate fact.

Unfold `Ranks.N`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `ea` using `(entry_bd hcL hN hW u τ j hj a).2`. Establish `eb` using `(entry_bd hcL hN hW u τ j hj b).1`.

Establish `: (2 * (((((D.fm u).lam j τ).w a : ℤ) : ℝ) - ((((D.fm u).lam j τ).w b : ℤ) : ℝ) + (D.R.N j : ℝ))) < ((D.mem u).A.T : ℝ)`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `this` after adjusting the coercions.
-/
theorem alcove_of {D : D7} {L : SizeData₂ D} {Cn cL : ℝ} (hcL : 1 ≤ cL) (hN : J.NumsL D L Cn cL) (hW : J.WtsL D L Cn)
    (hT : L.TuGe) (hm : 4 ≤ D.R.m) (u : D.what₂.Word) : product_first_zeroth_parts.Alcove D u := by
  intro j hj τ a b
  obtain ⟨s1, s2, s3, _, _, _, _⟩ := nums hcL u hN
  have hx1 := L.sc.one_lt_alt
  have hb24 : 24 ≤ L.sc.b := by linarith
  have hb1 : 1 ≤ L.sc.b := by linarith
  have hb'0 : 0 ≤ L.sc.b' := by linarith
  have hb2 : L.sc.b ^ 2 ≤ ((D.mem u).A.T : ℝ) := by
    refine le_trans ?_ (hT u)
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    push_cast
    linarith
  have hbb : L.sc.b ^ 2 = L.sc.b * L.sc.b := sq _
  have h24 : 24 * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right hb24 (by linarith)
  have h8 : 24 * L.sc.x * L.sc.b ≤ L.sc.b * L.sc.b := mul_le_mul_of_nonneg_right (s1.trans s2) (by linarith)
  have hq : L.sc.b' * L.sc.b' ≤ L.sc.b * L.sc.b := mul_le_mul s2 s2 hb'0 (by linarith)
  have hNj : (D.R.N j : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N j ≤ D.R.N D.R.m := by
      have := Nat.mul_le_mul_right (D.R.t + 1) hj
      unfold Ranks.N; omega
    exact_mod_cast this
  have ea := (entry_bd hcL hN hW u τ j hj a).2
  have eb := (entry_bd hcL hN hW u τ j hj b).1
  have : (2 * (((((D.fm u).lam j τ).w a : ℤ) : ℝ) - ((((D.fm u).lam j τ).w b : ℤ) : ℝ) + (D.R.N j : ℝ))) < ((D.mem u).A.T : ℝ) := by
    nlinarith
  exact_mod_cast this

end Formalism.MainNotions.GlobalTheoryTheory.Alc

end
