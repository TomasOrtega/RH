import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.TsumTruncatedShiftLe

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G
open scoped Classical

namespace Formalism.MainNotions.AuxBlock8.Pf

variable {D : D7} {L : SizeData₂ D}

structure GainBoundConstants (K : Consts) (Ce C bo : ℝ) : Prop where
  C3 : 3 ≤ C
  Cdl1 : 2 * K.dl1 + Ce ≤ C
  Cdl2 : 4 * K.dl2 ≤ C
  bo0 : 0 ≤ bo

/- English proof (translation)
Take `⟨hk, hN, hSc⟩` from `Nm_le_Sc P`. Establish `hn : 1 ≤ D.R.n` using `D.R.ord_pos`. Take `⟨hw1, hw2⟩` from `w''_le L.sc D.R.n hn`. Establish `hkS` using `P.kS_le`. Establish `hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `mul_le_mul_of_nonneg_right hk (by linarith)`.

Conclude with `⟨hk, hN, hSc, by linarith, by linarith, hw1, hw2, two_b'_le_a L.sc⟩`.
-/
theorem basics (P : ParameterChoice' D L) :
    (5 : ℝ) ≤ D.R.k ∧ Nm D ≤ L.Sc ∧ 100 ≤ L.Sc ∧ 500 ≤ L.sc.w'' D.R.n ∧ 5 * L.Sc ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧ L.sc.b' / L.sc.x ≤ L.sc.b' ∧ 2 * L.sc.b' ≤ L.sc.a := by
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n hn
  have hkS := P.kS_le
  have hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  exact ⟨hk, hN, hSc, by linarith, by linarith, hw1, hw2, two_b'_le_a L.sc⟩

/- English proof (translation)
Simplify using `[fill, hs]`.
-/
theorem fill_top (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (s : HH D) (hs : s ∈ D.host.TT) :
    fill X b j (false, s) = (b s : ℝ) + X.off j (false, s) := by
  simp [fill, hs]

/- English proof (translation)
Rewrite using `[fill_top X b j s hs]`. Establish `h1` using `hb s hs`. Establish `h2` using `(X.off_top j (false, s) ⟨rfl, hs⟩).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fill_top_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)) (j : ℕ) (s : HH D)
    (hs : s ∈ D.host.TT) : L.sc.b' + L.sc.b' / L.sc.x ≤ fill X b j (false, s) := by
  rw [fill_top X b j s hs]
  have h1 := hb s hs
  have h2 := (X.off_top j (false, s) ⟨rfl, hs⟩).1
  linarith

/- English proof (translation)
Take `⟨-, -, -, h500, -, hwb, hbb, -⟩` from `basics P`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Distinguish the cases in `ht : IsTopPl D z`. Take `⟨c, s⟩` from `z`. Take `⟨hz1, hz2⟩` from `ht`.

Simplify using `only at hz1 hz2`. Substitute `hz1` using the available equality. Establish `h1` using `fill_top_ge X b hb j s hz2`. Establish `h2 : 0 ≤ L.sc.b' / L.sc.x` using `by linarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hf : fill X b j z = X.off j z`. Unfold `fill`. Use `split_ifs with h`. Conclude with `absurd h ht`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hf]`. Distinguish the cases in `hk : IsThickPl D z`. Establish `h1` using `(X.off_thick j z hk).1`. Establish `hL : 1 ≤ L.sc.L`. Unfold `Scale.L`.

Conclude with `Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb2 : 2 ≤ L.sc.b`. Unfold `Scale.b`. Use `Real.add_one_le_exp L.sc.L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `(X.off_thin j z ⟨ht, hk⟩).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fill_ge_one (P : ParameterChoice' D L) (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ))
    (j : ℕ) (z : Bool × HH D) : 1 ≤ fill X b j z := by
  obtain ⟨-, -, -, h500, -, hwb, hbb, -⟩ := basics P
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  by_cases ht : IsTopPl D z
  · obtain ⟨c, s⟩ := z
    obtain ⟨hz1, hz2⟩ := ht
    simp only at hz1 hz2
    subst hz1
    have h1 := fill_top_ge X b hb j s hz2
    have h2 : 0 ≤ L.sc.b' / L.sc.x := by linarith
    linarith
  · have hf : fill X b j z = X.off j z := by
      unfold fill
      split_ifs with h
      · exact absurd h ht
      · ring
    rw [hf]
    by_cases hk : IsThickPl D z
    · have h1 := (X.off_thick j z hk).1
      have hL : 1 ≤ L.sc.L := by
        unfold Scale.L
        exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
      have hb2 : 2 ≤ L.sc.b := by
        unfold Scale.b
        have := Real.add_one_le_exp L.sc.L
        linarith
      linarith
    · have h1 := (X.off_thin j z ⟨ht, hk⟩).1
      linarith

/- English proof (translation)
Establish `hj1 : 1 ≤ j` using `(Finset.mem_Icc.mp hj).1`. Establish `hjr : (1 : ℝ) ≤ (j : ℝ)` using `by exact_mod_cast hj1`. Establish `hk : (0 : ℝ) ≤ (D.R.k : ℝ)` using `by positivity`. Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `by positivity`. Unfold `kaJ`.

Apply `div_nonneg _ (by norm_num)` to reduce the goal to its premises. Establish `hm : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)` using `mul_nonneg (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kaJ_nonneg (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : 0 ≤ kaJ D j := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  unfold kaJ
  apply div_nonneg _ (by norm_num)
  have hm : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

/- English proof (translation)
Take `⟨_, _, hSc, _⟩` from `basics P`. Establish `h1` using `fill_ge_one P X b hb j (partner D p s e)`. Establish `h2` using `kaJ_le P j hj`. Establish `h3` using `kaJ_nonneg (D := D) j hj`. Unfold `capU fillG cG`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem capU_bounds (P : ParameterChoice' D L) (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ))
    (p j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : HH D) (e : ℕ) :
    0 ≤ capU X b p j s e ∧ capU X b p j s e ≤ fill X b j (partner D p s e) + cG L := by
  obtain ⟨_, _, hSc, _⟩ := basics P
  have h1 := fill_ge_one P X b hb j (partner D p s e)
  have h2 := kaJ_le P j hj
  have h3 := kaJ_nonneg (D := D) j hj
  unfold capU fillG cG
  constructor <;> linarith

/- English proof (translation)
Take `⟨hk5, -, hSc, -, h5Sc, hwb, hbb, h2b⟩` from `basics P`. Take `⟨h1, h2, -⟩` from `hW s hs`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hxA : 1 ≤ L.sc.x ^ (Scale.A / 2)` using `Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)`. Establish `hden : 5 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)` using `by nlinarith`.

Establish `hapos : 0 < L.sc.a` using `by linarith`. Establish `hfrac : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5` using `div_le_div_of_nonneg_left hapos.le (by norm_num) hden`. Establish `hcG : 2 * cG L ≤ L.sc.a` using `by unfold cG; linarith`. Establish `hcG0 : 0 ≤ cG L` using `by unfold cG; linarith`. Unfold `al`.

Use `⟨h1, by linarith, by linarith, by linarith, by linarith⟩` and prove the remaining obligations.
-/
theorem a_bounds (P : ParameterChoice' D L) (a b : HH D → ℤ) (hW : InWin L a b) (s : HH D) (hs : s ∈ D.host.TT) :
    L.sc.a ≤ (a s : ℝ) ∧ (a s : ℝ) ≤ 6 / 5 * L.sc.a ∧ 2 * cG L ≤ (a s : ℝ) ∧ 0 ≤ al L a s ∧
      al L a s ≤ 6 / 5 * L.sc.a := by
  obtain ⟨hk5, -, hSc, -, h5Sc, hwb, hbb, h2b⟩ := basics P
  obtain ⟨h1, h2, -⟩ := hW s hs
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hxA : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)
  have hden : 5 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have hapos : 0 < L.sc.a := by linarith
  have hfrac : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left hapos.le (by norm_num) hden
  have hcG : 2 * cG L ≤ L.sc.a := by unfold cG; linarith
  have hcG0 : 0 ≤ cG L := by unfold cG; linarith
  unfold al
  refine ⟨h1, by linarith, by linarith, by linarith, by linarith⟩

/- English proof (translation)
Establish `hx : 1 < s.x` using `s.one_lt_alt`. Establish `hL : 1 ≤ s.L`. Unfold `Scale.L`. Conclude with `Real.one_le_rpow hx.le s.eps_pos.le`. Establish `hb : 2 ≤ s.b`.

Unfold `Scale.b`. Use `Real.add_one_le_exp s.L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Scale.a`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_a (s : Scale) : 2 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 1 ≤ s.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx.le s.eps_pos.le
  have hb : 2 ≤ s.b := by
    unfold Scale.b
    have := Real.add_one_le_exp s.L
    linarith
  unfold Scale.a
  nlinarith

/- English proof (translation)
Establish `ha` using `two_le_a s`. Establish `hp1 : (1 : ℝ) < (p : ℝ)` using `by exact_mod_cast hp.one_lt`. Use `⟨Real.logb_nonneg hp1 (by linarith), Real.logb_nonneg hp1 (by linarith), ?_⟩` and prove the remaining obligations. Rewrite using `[Real.logb_mul (by norm_num) (ne_of_gt (by linarith))]`. Establish `h2 : Real.logb p 2 ≤ Real.logb p s.a` using `Real.logb_le_logb_of_le hp1 (by norm_num) ha`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logb_facts (s : Scale) (p : ℕ) (hp : p.Prime) :
    0 ≤ Real.logb p s.a ∧ 0 ≤ Real.logb p (2 * s.a) ∧ Real.logb p (2 * s.a) ≤ 2 * Real.logb p s.a := by
  have ha := two_le_a s
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  refine ⟨Real.logb_nonneg hp1 (by linarith), Real.logb_nonneg hp1 (by linarith), ?_⟩
  rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith))]
  have h2 : Real.logb p 2 ≤ Real.logb p s.a := Real.logb_le_logb_of_le hp1 (by norm_num) ha
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -, -⟩` from `hK`. Establish `hl` using `(logb_facts L.sc p hp).2.1`. Unfold `dl`. Establish `a1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a)` using `mul_nonneg (mul_nonneg (mul_nonneg h1 (by positivity)) (sq_nonneg _)) hl`. Establish `a2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2` using `mul_nonneg (mul_nonneg h2 (by positivity)) (sq_nonneg _)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dl_nonneg (X : Inst D L) (K : Consts) (hK : K.Nonneg) (p : ℕ) (hp : p.Prime) (t0 : HH D) :
    0 ≤ dl X K p t0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -, -⟩ := hK
  have hl := (logb_facts L.sc p hp).2.1
  unfold dl
  have a1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) :=
    mul_nonneg (mul_nonneg (mul_nonneg h1 (by positivity)) (sq_nonneg _)) hl
  have a2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 :=
    mul_nonneg (mul_nonneg h2 (by positivity)) (sq_nonneg _)
  linarith

/- English proof (translation)
Unfold `topsOn at hs`. Conclude with `(Finset.mem_filter.mp hs).1`.
-/
theorem mem_TT_of_topsOn (X : Inst D L) (p : ℕ) (t0 s : HH D) (hs : s ∈ topsOn X p t0) : s ∈ D.host.TT := by
  unfold topsOn at hs
  exact (Finset.mem_filter.mp hs).1

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ (p : ℝ)` using `by exact_mod_cast hp.two_le`. Establish `hp0 : 0 < (p : ℝ)` using `by linarith`. Establish `hden : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Unfold `gam`. Prove the components needed by the constructor for the conclusion.

Conclude with `div_nonneg hp0.le hden.le`. Rewrite using `[div_le_iff₀ hden]`. Establish `e : 4 / 3 * (1 / (p : ℝ)) * ((p : ℝ) ^ 2 - 1) = (4 * ((p : ℝ) ^ 2 - 1) / 3) / (p : ℝ)` using `by ring`. Rewrite using `[e, le_div_iff₀ hp0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gam_facts (p : ℕ) (hp : p.Prime) : 0 ≤ gam p ∧ gam p ≤ 4 / 3 * (1 / p) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  unfold gam
  constructor
  · exact div_nonneg hp0.le hden.le
  · rw [div_le_iff₀ hden]
    have e : 4 / 3 * (1 / (p : ℝ)) * ((p : ℝ) ^ 2 - 1) = (4 * ((p : ℝ) ^ 2 - 1) / 3) / (p : ℝ) := by ring
    rw [e, le_div_iff₀ hp0]
    nlinarith

/- English proof (translation)
Unfold `gU`. Use `le_trans (sub_le_self _ (dl_nonneg X K hK p hp t0)) (sub_le_self _ ?_)` and prove the remaining obligations. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `s hs`. Apply `tsum_nonneg` to reduce the goal to its premises.

Introduce `e`. Use `split_ifs`. Apply `le_min` to reduce the goal to its premises. Conclude with `div_nonneg (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s (Finset.mem_filter.1 hs).1)).2.2.2.1 (by positivity)`. Conclude with `(capU_bounds P X b (fun t ht => (hW t ht).2.2) p j hj s e).1`.

Conclude with `le_rfl`.
-/
theorem gU_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (a b : HH D → ℤ) (hW : InWin L a b)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    gU X K a b p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := by
  unfold gU
  refine le_trans (sub_le_self _ (dl_nonneg X K hK p hp t0)) (sub_le_self _ ?_)
  apply Finset.sum_nonneg
  intro s hs
  apply tsum_nonneg
  intro e
  split_ifs
  · apply le_min
    · exact div_nonneg (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s (Finset.mem_filter.1 hs).1)).2.2.2.1
        (by positivity)
    · exact (capU_bounds P X b (fun t ht => (hW t ht).2.2) p j hj s e).1
  · exact le_rfl

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Unfold `g0`. Use `le_trans (sub_le_self _ (dl_nonneg X K hK p hp t0)) ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `s hs`. Unfold `gam`. Conclude with `@tsum_pos_le (p : ℝ) (al L a s) hp2 (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)).2.2.2.1 (fun e => capU X b p j s e) (fun e => (capU_bounds P X b (fun t ht => (hW t ht).2.2) p j hj s e).1) (fun e => Odd e ∧ ¬ Excl D p s e) _ (fun e h => h.1)`.
-/
theorem g_zero_le_gamma_sum (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (a b : HH D → ℤ) (hW : InWin L a b)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    g0 X K a b p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold g0
  refine le_trans (sub_le_self _ (dl_nonneg X K hK p hp t0)) ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  unfold gam
  exact @tsum_pos_le (p : ℝ) (al L a s) hp2 (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)).2.2.2.1
    (fun e => capU X b p j s e) (fun e => (capU_bounds P X b (fun t ht => (hW t ht).2.2) p j hj s e).1)
    (fun e => Odd e ∧ ¬ Excl D p s e) _ (fun e h => h.1)

/- English proof (translation)
Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hPr1, hPr2⟩` from `hK`. Take `⟨hk, hNm, hSc, hw500, h5, hw1, hw2, hab⟩` from `basics P`. Establish `hη` using `L.etaSz_pos`. Establish `hb'` using `sc_b'_nonneg L.sc`. Establish `hNm0 : 0 ≤ Nm D` using `by unfold Nm; exact Nat.cast_nonneg _`.

Establish `hcG : 0 ≤ cG L` using `by unfold cG; linarith`. Establish `hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D` using `by linarith`. Unfold `Pr`. Use `split_ifs with h0`. Apply `add_nonneg` to reduce the goal to its premises.

Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `s hs`. Establish `hs'` using `mem_TT_of_topsOn X p t0 s (Finset.mem_filter.1 hs).1`. Establish `h2` using `(X.off_top j (false, s) ⟨rfl, hs'⟩).1`. Establish `h3` using `kaJ_le P j hj`.

Unfold `fillG`. Rewrite using `[fill_top X b j s hs']`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))`.
-/
theorem Pr_nonneg (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (b : HH D → ℤ)
    (p : ℕ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) : 0 ≤ Pr X K b p j t0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hPr1, hPr2⟩ := hK
  obtain ⟨hk, hNm, hSc, hw500, h5, hw1, hw2, hab⟩ := basics P
  have hη := L.etaSz_pos
  have hb' := sc_b'_nonneg L.sc
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D := by linarith
  unfold Pr
  split_ifs with h0
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro s hs
      have hs' := mem_TT_of_topsOn X p t0 s (Finset.mem_filter.1 hs).1
      have h2 := (X.off_top j (false, s) ⟨rfl, hs'⟩).1
      have h3 := kaJ_le P j hj
      unfold fillG
      rw [fill_top X b j s hs']
      linarith
    · exact mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase
  · exact mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))

/- English proof (translation)
Unfold `topsOn reps`. Rewrite using `[Finset.sum_fiberwise_of_maps_to]`. Introduce `x _`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ x)`.
-/
theorem sum_reps (X : Inst D L) (p : ℕ) (f : HH D → ℝ) :
    ∑ t0 ∈ reps X p, ∑ s ∈ topsOn X p t0, f s = ∑ s ∈ D.host.TT, f s := by
  unfold topsOn reps
  rw [Finset.sum_fiberwise_of_maps_to]
  intro x _
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

/- English proof (translation)
Unfold `VV`. Use `split_ifs`. Unfold `goodReps`. Conclude with `Finset.filter_subset _ _`. Conclude with `Finset.empty_subset _`.
-/
theorem VV_subset_reps (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : VV X K a b p ⊆ reps X p := by
  unfold VV
  split_ifs
  · unfold goodReps
    exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]`.
-/
theorem bs_nsmul (X : Inst D L) (h t : HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

/- English proof (translation)
Take `⟨i, hi⟩` from `X.bs_orb h t`. Establish `e` using `bs_nsmul X h (X.bs h t) i`. Rewrite `e` using `[hi]`. Conclude with `e.symm`.
-/
theorem bs_bs (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  have e := bs_nsmul X h (X.bs h t) i
  rw [hi] at e
  exact e.symm

/- English proof (translation)
Establish `hcard : Fintype.card (HH D) = D.R.n` using `D.R.card_A`. Establish `h1 : (Finset.univ : Finset (HH D)).card = ∑ t0 ∈ reps X p, (Finset.univ.filter (fun t => X.bs (stepP D p) t = t0)).card` using `Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_image_of_mem _ (Finset.mem_univ s))`. Establish `h2 : ∀ t0 ∈ reps X p, addOrderOf (stepP D p) ≤ (Finset.univ.filter (fun t => X.bs (stepP D p) t = t0)).card`. Introduce `t0 ht0`. Take `⟨t, _, rfl⟩` from `Finset.mem_image.1 ht0`.

Use `Finset.card_le_card_of_injOn (s := Finset.range (addOrderOf (stepP D p))) (t := Finset.univ.filter (fun t' => X.bs (stepP D p) t' = X.bs (stepP D p) t)) (fun i => X.bs (stepP D p) t + i • stepP D p) (fun i _ => by` as an intermediate fact. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]`. Rewrite using `[bs_nsmul, bs_bs])`. Use the proof step `(fun i hi i' hi' hii => by`. Establish `hi1 : i ∈ Set.Iio (addOrderOf (stepP D p))` using `by simpa using hi`.

Establish `hi2 : i' ∈ Set.Iio (addOrderOf (stepP D p))` using `by simpa using hi'`. Conclude with `nsmul_injOn_Iio_addOrderOf hi1 hi2 (add_left_cancel hii))`. Simplify using `using this`. Establish `h3` using `Finset.sum_le_sum h2`. Rewrite `h3` using `[Finset.sum_const, smul_eq_mul, ← h1, Finset.card_univ, hcard]`.

Conclude with `h3`.
-/
theorem card_reps_mul_le (X : Inst D L) (p : ℕ) : (reps X p).card * addOrderOf (stepP D p) ≤ D.R.n := by
  classical
  have hcard : Fintype.card (HH D) = D.R.n := D.R.card_A
  have h1 : (Finset.univ : Finset (HH D)).card =
      ∑ t0 ∈ reps X p, (Finset.univ.filter (fun t => X.bs (stepP D p) t = t0)).card :=
    Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_image_of_mem _ (Finset.mem_univ s))
  have h2 : ∀ t0 ∈ reps X p, addOrderOf (stepP D p) ≤
      (Finset.univ.filter (fun t => X.bs (stepP D p) t = t0)).card := by
    intro t0 ht0
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ht0
    have := Finset.card_le_card_of_injOn (s := Finset.range (addOrderOf (stepP D p)))
      (t := Finset.univ.filter (fun t' => X.bs (stepP D p) t' = X.bs (stepP D p) t))
      (fun i => X.bs (stepP D p) t + i • stepP D p)
      (fun i _ => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [bs_nsmul, bs_bs])
      (fun i hi i' hi' hii => by
        have hi1 : i ∈ Set.Iio (addOrderOf (stepP D p)) := by simpa using hi
        have hi2 : i' ∈ Set.Iio (addOrderOf (stepP D p)) := by simpa using hi'
        exact nsmul_injOn_Iio_addOrderOf hi1 hi2 (add_left_cancel hii))
    simpa using this
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_const, smul_eq_mul, ← h1, Finset.card_univ, hcard] at h3
  exact h3

/- English proof (translation)
Establish `h` using `card_reps_mul_le X p`. Establish `hf : D.R.f = 2 * D.R.n` using `rfl`. Distinguish the cases in `hs : IsSg D p`. Establish `h1 : stepP D p = 2 • hP D p` using `by unfold stepP; rw [if_pos hs]`. Establish `h2 : nP D p = 2 * addOrderOf (2 • hP D p)` using `by unfold nP; rw [if_pos hs]`.

Rewrite `h` using `[h1]`. Rewrite using `[h2, hf]`. Establish `: (reps X p).card * (2 * addOrderOf (2 • hP D p)) ≤ 2 * D.R.n` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Establish `h1 : stepP D p = hP D p` using `by unfold stepP; rw [if_neg hs]`.

Establish `h2 : nP D p = addOrderOf (hP D p)` using `by unfold nP; rw [if_neg hs]`. Rewrite `h` using `[h1]`. Rewrite using `[h2, hf]`. Establish `: (reps X p).card * addOrderOf (hP D p) ≤ 2 * D.R.n` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem card_reps_mul_nP_le (X : Inst D L) (p : ℕ) : ((reps X p).card : ℝ) * (nP D p : ℝ) ≤ (D.R.f : ℝ) := by
  have h := card_reps_mul_le X p
  have hf : D.R.f = 2 * D.R.n := rfl
  by_cases hs : IsSg D p
  · have h1 : stepP D p = 2 • hP D p := by unfold stepP; rw [if_pos hs]
    have h2 : nP D p = 2 * addOrderOf (2 • hP D p) := by unfold nP; rw [if_pos hs]
    rw [h1] at h
    rw [h2, hf]
    have : (reps X p).card * (2 * addOrderOf (2 • hP D p)) ≤ 2 * D.R.n := by nlinarith
    exact_mod_cast this
  · have h1 : stepP D p = hP D p := by unfold stepP; rw [if_neg hs]
    have h2 : nP D p = addOrderOf (hP D p) := by unfold nP; rw [if_neg hs]
    rw [h1] at h
    rw [h2, hf]
    have : (reps X p).card * addOrderOf (hP D p) ≤ 2 * D.R.n := by omega
    exact_mod_cast this

/- English proof (translation)
Establish `h` using `sum_reps X p (fun _ => (1 : ℝ))`. Simplify using `only [Finset.sum_const, nsmul_eq_mul, mul_one] at h`. Unfold `Nv`. Conclude with `h`.
-/
theorem sum_Nv (X : Inst D L) (p : ℕ) : ∑ t0 ∈ reps X p, (Nv X p t0 : ℝ) = (D.host.TT.card : ℝ) := by
  have h := sum_reps X p (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  unfold Nv
  exact h

/- English proof (translation)
Establish `h1 : D.host.TT.card ≤ Fintype.card (HH D)` using `Finset.card_le_univ _`. Establish `h2 : Fintype.card (HH D) = D.R.n` using `D.R.card_A`. Establish `hf : D.R.f = 2 * D.R.n` using `rfl`. Establish `: D.host.TT.card ≤ D.R.f` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem card_TT_le_f (D : D7) : (D.host.TT.card : ℝ) ≤ (D.R.f : ℝ) := by
  have h1 : D.host.TT.card ≤ Fintype.card (HH D) := Finset.card_le_univ _
  have h2 : Fintype.card (HH D) = D.R.n := D.R.card_A
  have hf : D.R.f = 2 * D.R.n := rfl
  have : D.host.TT.card ≤ D.R.f := by omega
  exact_mod_cast this

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -, -⟩` from `hK`. Take `⟨hl0, hl20, hl2⟩` from `logb_facts L.sc p hp`. Establish `hR` using `card_reps_mul_nP_le X p`. Establish `hN` using `sum_Nv X p`. Establish `hT` using `card_TT_le_f D`.

Establish `hsum : ∑ t0 ∈ reps X p, dl X K p t0 = K.dl1 * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * (((reps X p).card : ℝ) * (nP D p : ℝ)) + K.dl2 * Real.logb p (2 * L.sc.a) ^ 2 * ∑ t0 ∈ reps X p, (Nv X p t0 : ℝ)`. Unfold `dl`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `Finset.sum_congr rfl (fun _ _ => by ring)`. Establish `c0 : 0 ≤ K.dl1 * Nm D ^ 2` using `mul_nonneg h1 (sq_nonneg _)`. Establish `t1 : K.dl1 * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * (((reps X p).card : ℝ) * (nP D p : ℝ)) ≤ K.dl1 * Nm D ^ 2 * (2 * Real.logb p L.sc.a) * (D.R.f : ℝ)` using `mul_le_mul (mul_le_mul_of_nonneg_left hl2 c0) hR (by positivity) (mul_nonneg c0 (by linarith))`. Establish `hB2 : Real.logb p (2 * L.sc.a) ^ 2 ≤ (2 * Real.logb p L.sc.a) ^ 2` using `by nlinarith`. Establish `t2 : K.dl2 * Real.logb p (2 * L.sc.a) ^ 2 * ∑ t0 ∈ reps X p, (Nv X p t0 : ℝ) ≤ K.dl2 * (2 * Real.logb p L.sc.a) ^ 2 * (D.R.f : ℝ)`.

Rewrite using `[hN]`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left hB2 h2) hT (by positivity) (mul_nonneg h2 (sq_nonneg _))`. Rewrite using `[hsum]`. Use polynomial arithmetic with `[t1, t2]`.
-/
theorem sum_dl_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (p : ℕ) (hp : p.Prime) :
    ∑ t0 ∈ reps X p, dl X K p t0 ≤ 2 * K.dl1 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a +
      4 * K.dl2 * (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -, -⟩ := hK
  obtain ⟨hl0, hl20, hl2⟩ := logb_facts L.sc p hp
  have hR := card_reps_mul_nP_le X p
  have hN := sum_Nv X p
  have hT := card_TT_le_f D
  have hsum : ∑ t0 ∈ reps X p, dl X K p t0 =
      K.dl1 * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * (((reps X p).card : ℝ) * (nP D p : ℝ)) +
      K.dl2 * Real.logb p (2 * L.sc.a) ^ 2 * ∑ t0 ∈ reps X p, (Nv X p t0 : ℝ) := by
    unfold dl
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun _ _ => by ring)
  have c0 : 0 ≤ K.dl1 * Nm D ^ 2 := mul_nonneg h1 (sq_nonneg _)
  have t1 : K.dl1 * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * (((reps X p).card : ℝ) * (nP D p : ℝ)) ≤
      K.dl1 * Nm D ^ 2 * (2 * Real.logb p L.sc.a) * (D.R.f : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl2 c0) hR (by positivity) (mul_nonneg c0 (by linarith))
  have hB2 : Real.logb p (2 * L.sc.a) ^ 2 ≤ (2 * Real.logb p L.sc.a) ^ 2 := by nlinarith
  have t2 : K.dl2 * Real.logb p (2 * L.sc.a) ^ 2 * ∑ t0 ∈ reps X p, (Nv X p t0 : ℝ) ≤
      K.dl2 * (2 * Real.logb p L.sc.a) ^ 2 * (D.R.f : ℝ) := by
    rw [hN]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB2 h2) hT (by positivity) (mul_nonneg h2 (sq_nonneg _))
  rw [hsum]
  nlinarith [t1, t2]

/- English proof (translation)
Establish `h` using `(logb_facts s p hp).1`. Establish `hf : (0 : ℝ) ≤ (D.R.f : ℝ)` using `by positivity`. Unfold `fl`. Establish `h1 : 0 ≤ C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a` using `mul_nonneg (mul_nonneg (mul_nonneg hC hf) (sq_nonneg _)) h`. Establish `h2 : 0 ≤ C * (D.R.f : ℝ) * Real.logb p s.a ^ 2` using `mul_nonneg (mul_nonneg hC hf) (sq_nonneg _)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fl_nonneg (s : Scale) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) : 0 ≤ fl D s C p := by
  have h := (logb_facts s p hp).1
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
  unfold fl
  have h1 : 0 ≤ C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hf) (sq_nonneg _)) h
  have h2 : 0 ≤ C * (D.R.f : ℝ) * Real.logb p s.a ^ 2 := mul_nonneg (mul_nonneg hC hf) (sq_nonneg _)
  linarith

/- English proof (translation)
Establish `h1` using `sum_dl_le X K hK p hp`. Take `⟨hlg, _, _⟩` from `logb_facts L.sc p hp`. Establish `hf0 : (0 : ℝ) ≤ (D.R.f : ℝ)` using `Nat.cast_nonneg _`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)` using `Nat.cast_nonneg _`. Establish `hkN : (D.R.k : ℝ) ≤ Nm D`.

Establish `: D.R.k ≤ D.R.N D.R.m` using `by unfold Ranks.N; omega`. Unfold `Nm`. Conclude with `this` after adjusting the coercions. Establish `hk2 : (D.R.k : ℝ) ^ 2 ≤ Nm D ^ 2` using `pow_le_pow_left₀ hk0 hkN 2`. Establish `h2 : Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a ≤ Ce * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 (mul_nonneg hCe hf0)) hlg`.

Establish `h3 : (2 * K.dl1 + Ce) * ((D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) ≤ C * ((D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a)` using `mul_le_mul_of_nonneg_right hN.Cdl1 (mul_nonneg (mul_nonneg hf0 (sq_nonneg _)) hlg)`. Establish `h4 : (4 * K.dl2) * ((D.R.f : ℝ) * Real.logb p L.sc.a ^ 2) ≤ C * ((D.R.f : ℝ) * Real.logb p L.sc.a ^ 2)` using `mul_le_mul_of_nonneg_right hN.Cdl2 (mul_nonneg hf0 (sq_nonneg _))`. Unfold `fl`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_dl_add_ep_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hCe : 0 ≤ Ce)
    (hN : GainBoundConstants K Ce C bo) (p : ℕ) (hp : p.Prime)
    (h9 : (X.ep p : ℝ) ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) :
    ∑ t0 ∈ reps X p, dl X K p t0 + (X.ep p : ℝ) ≤ fl D L.sc C p := by
  have h1 := sum_dl_le X K hK p hp
  obtain ⟨hlg, _, _⟩ := logb_facts L.sc p hp
  have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ Nm D := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    unfold Nm
    exact_mod_cast this
  have hk2 : (D.R.k : ℝ) ^ 2 ≤ Nm D ^ 2 := pow_le_pow_left₀ hk0 hkN 2
  have h2 : Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a ≤
      Ce * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 (mul_nonneg hCe hf0)) hlg
  have h3 : (2 * K.dl1 + Ce) * ((D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) ≤
      C * ((D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) :=
    mul_le_mul_of_nonneg_right hN.Cdl1 (mul_nonneg (mul_nonneg hf0 (sq_nonneg _)) hlg)
  have h4 : (4 * K.dl2) * ((D.R.f : ℝ) * Real.logb p L.sc.a ^ 2) ≤
      C * ((D.R.f : ℝ) * Real.logb p L.sc.a ^ 2) :=
    mul_le_mul_of_nonneg_right hN.Cdl2 (mul_nonneg hf0 (sq_nonneg _))
  unfold fl
  nlinarith

/- English proof (translation)
Establish `h0` using `hK.1`. Establish `ha` using `two_le_a s`. Unfold `La`. Establish `hl : 0 ≤ Real.log s.a` using `Real.log_nonneg (by linarith)`. Conclude with `mul_nonneg (mul_nonneg h0 (sq_nonneg _)) hl`.
-/
theorem La_nonneg (K : Consts) (hK : K.Nonneg) (s : Scale) : 0 ≤ La K s := by
  have h0 := hK.1
  have ha := two_le_a s
  unfold La
  have hl : 0 ≤ Real.log s.a := Real.log_nonneg (by linarith)
  exact mul_nonneg (mul_nonneg h0 (sq_nonneg _)) hl

/- English proof (translation)
Take `⟨_, hlg2, _⟩` from `logb_facts L.sc p hp`. Take `⟨_, _, hSc, hw500, _⟩` from `basics P`. Establish `hC0 : 0 ≤ C` using `le_trans (by norm_num) hN.C3`. Establish `hη` using `L.etaSz_pos`. Establish `hcG : 0 ≤ cG L` using `by unfold cG; linarith`.

Establish `hb'` using `sc_b'_nonneg L.sc`. Establish `hx` using `sc_x_pos L.sc`. Establish `ha : 0 ≤ L.sc.a` using `le_trans zero_le_one (sc_one_lt_a L.sc).le`. Establish `hlx : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg L.sc.one_lt_alt.le`. Establish `hd` using `sc_delta1_pos L.sc`.

Establish `hLa` using `La_nonneg K hK L.sc`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ)` using `Nat.cast_nonneg _`. Establish `hcp : 3 * cG L * Real.logb p (2 * L.sc.a) ≤ C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)`. Apply `mul_le_mul_of_nonneg_right _ hlg2` to reduce the goal to its premises.

Use polynomial arithmetic with `[hN.C3]`. Simplify using `only [lo]`. Apply `le_add_of_le_of_nonneg` to reduce the goal to its premises. Apply `le_add_of_le_of_nonneg hcp split_ifs` to reduce the goal to its premises. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) hb') hlx`.

Establish `h1 : 0 ≤ L.sc.b' / L.sc.x` using `div_nonneg hb' hx.le`. Establish `h2 : 0 ≤ C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1` using `div_nonneg (mul_nonneg (mul_nonneg hC0 (by linarith)) hlx) hd.le`. Use `hN.bo0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`.

Conclude with `le_rfl`. Establish `h0 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)` using `div_nonneg (mul_nonneg hLa ha) (mul_nonneg hp0.le hk0) split_ifs`. Conclude with `mul_nonneg (mul_nonneg hC0 hlx) (add_nonneg h0 (mul_nonneg ha (Real.rpow_nonneg hp0.le _)))`. Conclude with `mul_nonneg (mul_nonneg hC0 hlx) (add_nonneg h0 (div_nonneg ha (by positivity)))`. Conclude with `le_rfl`.
-/
theorem lo_ge_cp (P : ParameterChoice' D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hN : GainBoundConstants K Ce C bo) (p : ℕ)
    (hp : p.Prime) : 3 * cG L * Real.logb p (2 * L.sc.a) ≤ lo K L C bo p := by
  obtain ⟨_, hlg2, _⟩ := logb_facts L.sc p hp
  obtain ⟨_, _, hSc, hw500, _⟩ := basics P
  have hC0 : 0 ≤ C := le_trans (by norm_num) hN.C3
  have hη := L.etaSz_pos
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hb' := sc_b'_nonneg L.sc
  have hx := sc_x_pos L.sc
  have ha : 0 ≤ L.sc.a := le_trans zero_le_one (sc_one_lt_a L.sc).le
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hd := sc_delta1_pos L.sc
  have hLa := La_nonneg K hK L.sc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have hcp : 3 * cG L * Real.logb p (2 * L.sc.a) ≤ C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) := by
    apply mul_le_mul_of_nonneg_right _ hlg2
    nlinarith [hN.C3]
  dsimp only [lo]
  apply le_add_of_le_of_nonneg
  · apply le_add_of_le_of_nonneg hcp
    split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) hb') hlx
    · have h1 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb' hx.le
      have h2 : 0 ≤ C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
        div_nonneg (mul_nonneg (mul_nonneg hC0 (by linarith)) hlx) hd.le
      have := hN.bo0
      linarith
    · exact le_rfl
    · exact le_rfl
  · have h0 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) := div_nonneg (mul_nonneg hLa ha) (mul_nonneg hp0.le hk0)
    split_ifs
    · exact mul_nonneg (mul_nonneg hC0 hlx) (add_nonneg h0 (mul_nonneg ha (Real.rpow_nonneg hp0.le _)))
    · exact mul_nonneg (mul_nonneg hC0 hlx) (add_nonneg h0 (div_nonneg ha (by positivity)))
    · exact le_rfl

/- English proof (translation)
Take `⟨_, hlg2, _⟩` from `logb_facts L.sc p hp`. Take `⟨_, _, hSc, _⟩` from `basics P`. Establish `hcG : 0 ≤ cG L` using `by unfold cG; linarith`. Conclude with `le_trans (mul_nonneg (mul_nonneg (by norm_num) hcG) hlg2) (lo_ge_cp P K hK Ce C bo hN p hp)`.
-/
theorem lo_nonneg (P : ParameterChoice' D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hN : GainBoundConstants K Ce C bo) (p : ℕ)
    (hp : p.Prime) : 0 ≤ lo K L C bo p := by
  obtain ⟨_, hlg2, _⟩ := logb_facts L.sc p hp
  obtain ⟨_, _, hSc, _⟩ := basics P
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  exact le_trans (mul_nonneg (mul_nonneg (by norm_num) hcG) hlg2) (lo_ge_cp P K hK Ce C bo hN p hp)

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Take `⟨_, _, hSc, _⟩` from `basics P`. Establish `hcG : 0 ≤ cG L` using `by unfold cG; linarith`. Establish `hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)` using `fun t ht => (hW t ht).2.2`. Unfold `g0`.

Apply `sub_le_sub_right` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `s hs`. Take `⟨ha1, ha2, ha3, _, _⟩` from `a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)`. Establish `ha` using `sc_one_lt_a L.sc`.

Establish `hask : askP X a b p j s = ∑' e : ℕ, if Odd e ∧ ¬ Excl D p s e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - fill X b j (partner D p s e)) else 0`. Unfold `askP`. Use `congr 1`. Use function extensionality and compare the values at `e`. Distinguish the cases in `ho : Odd e`.

Distinguish the cases in `hx : Excl D p s e`. Rewrite using `[if_pos ho, if_neg (fun h => h.2 hx), max_eq_left (by linarith [hEx s hs e hx])]`. Rewrite using `[if_pos ho, if_pos ⟨ho, hx⟩]`. Rewrite using `[if_neg ho, if_neg (fun h => ho h.1)]`. Rewrite using `[hask]`.

Unfold `al`. Conclude with `@tsum_truncated_shift_le (p : ℝ) (a s : ℝ) (cG L) (2 * L.sc.a) hp2 hcG ha3 (by linarith) (by linarith) (fun e => fill X b j (partner D p s e)) (fun e => capU X b p j s e) (fun e => fill_ge_one P X b hb j _) (fun e => (capU_bounds P X b hb p j hj s e).1) (fun e => (capU_bounds P X …`.
-/
theorem g_zero_ge_ask_sum (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (hW : InWin L a b)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t0 : HH D)
    (hEx : ∀ s ∈ topsOn X p t0, ∀ e, Excl D p s e → (a s : ℝ) / (p : ℝ) ^ e ≤ fill X b j (partner D p s e)) :
    ∑ s ∈ topsOn X p t0, (askP X a b p j s - 3 * cG L * Real.logb p (2 * L.sc.a)) - dl X K p t0 ≤
      g0 X K a b p j t0 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨_, _, hSc, _⟩ := basics P
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (hW t ht).2.2
  unfold g0
  apply sub_le_sub_right
  apply Finset.sum_le_sum
  intro s hs
  obtain ⟨ha1, ha2, ha3, _, _⟩ := a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)
  have ha := sc_one_lt_a L.sc
  have hask : askP X a b p j s = ∑' e : ℕ, if Odd e ∧ ¬ Excl D p s e then
      max 0 ((a s : ℝ) / (p : ℝ) ^ e - fill X b j (partner D p s e)) else 0 := by
    unfold askP
    congr 1
    funext e
    by_cases ho : Odd e
    · by_cases hx : Excl D p s e
      · rw [if_pos ho, if_neg (fun h => h.2 hx), max_eq_left (by linarith [hEx s hs e hx])]
      · rw [if_pos ho, if_pos ⟨ho, hx⟩]
    · rw [if_neg ho, if_neg (fun h => ho h.1)]
  rw [hask]
  unfold al
  exact @tsum_truncated_shift_le (p : ℝ) (a s : ℝ) (cG L) (2 * L.sc.a) hp2 hcG ha3 (by linarith) (by linarith)
    (fun e => fill X b j (partner D p s e)) (fun e => capU X b p j s e)
    (fun e => fill_ge_one P X b hb j _) (fun e => (capU_bounds P X b hb p j hj s e).1)
    (fun e => (capU_bounds P X b hb p j hj s e).2) (fun e => Odd e ∧ ¬ Excl D p s e) _ (fun e h => h.1)

/- English proof (translation)
Simplify using `[SizeData₂.lifts]`.
-/
theorem card_lifts (D : D7) : ((SizeData₂.lifts D).card : ℝ) = (D.R.m : ℝ) := by
  simp [SizeData₂.lifts]

/- English proof (translation)
Establish `hfl : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, (askP X a b p j s - lo K L C bo p) ≤ (∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0) + fl D L.sc C p`. Introduce `j hj`. Establish `hlo` using `lo_ge_cp P K hK Ce C bo hN p hp`. Establish `hdl` using `sum_dl_add_ep_le X K hK Ce C bo hCe hN p hp h9`. Establish `hep : (0 : ℝ) ≤ (X.ep p : ℝ)` using `by positivity`.

Rewrite using `[← sum_reps X p]`. Establish `hper : ∀ t0 ∈ reps X p, ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p) ≤ max (g0 X K a b p j t0) 0 + dl X K p t0`. Introduce `t0 _`. Establish `hg` using `g_zero_ge_ask_sum P X K a b hW p hp j hj t0 (fun s hs e hx => hEx j hj s (mem_TT_of_topsOn X p t0 s hs) e hx)`. Establish `hmono : ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p) ≤ ∑ s ∈ topsOn X p t0, (askP X a b p j s - 3 * cG L * Real.logb p (2 * L.sc.a))` using `Finset.sum_le_sum (fun s _ => by linarith)`.

Establish `hmx` using `le_max_left (g0 X K a b p j t0) 0`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `htot` using `Finset.sum_le_sum hfl`. Rewrite `htot` using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_lifts D]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem noop (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hCe : 0 ≤ Ce)
    (hN : GainBoundConstants K Ce C bo) (a b : HH D → ℤ) (hW : InWin L a b) (p : ℕ) (hp : p.Prime)
    (h9 : (X.ep p : ℝ) ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a)
    (hEx : ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ D.host.TT, ∀ e, Excl D p s e →
      (a s : ℝ) / (p : ℝ) ^ e ≤ fill X b j (partner D p s e)) :
    (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, (askP X a b p j s - lo K L C bo p)) - (D.R.m : ℝ) * fl D L.sc C p ≤
      ∑ j ∈ SizeData₂.lifts D, ∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0 := by
  have hfl : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, (askP X a b p j s - lo K L C bo p) ≤
      (∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0) + fl D L.sc C p := by
    intro j hj
    have hlo := lo_ge_cp P K hK Ce C bo hN p hp
    have hdl := sum_dl_add_ep_le X K hK Ce C bo hCe hN p hp h9
    have hep : (0 : ℝ) ≤ (X.ep p : ℝ) := by positivity
    rw [← sum_reps X p]
    have hper : ∀ t0 ∈ reps X p, ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p) ≤
        max (g0 X K a b p j t0) 0 + dl X K p t0 := by
      intro t0 _
      have hg := g_zero_ge_ask_sum P X K a b hW p hp j hj t0
        (fun s hs e hx => hEx j hj s (mem_TT_of_topsOn X p t0 s hs) e hx)
      have hmono : ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p) ≤
          ∑ s ∈ topsOn X p t0, (askP X a b p j s - 3 * cG L * Real.logb p (2 * L.sc.a)) :=
        Finset.sum_le_sum (fun s _ => by linarith)
      have hmx := le_max_left (g0 X K a b p j t0) 0
      linarith
    calc ∑ t0 ∈ reps X p, ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p)
        ≤ ∑ t0 ∈ reps X p, (max (g0 X K a b p j t0) 0 + dl X K p t0) := Finset.sum_le_sum hper
      _ = (∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0) + ∑ t0 ∈ reps X p, dl X K p t0 :=
          Finset.sum_add_distrib
      _ ≤ (∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0) + fl D L.sc C p := by linarith
  have htot := Finset.sum_le_sum hfl
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_lifts D] at htot
  linarith

/- English proof (translation)
Establish `hg` using `(gam_facts p hp).1`. Establish `hsum : 0 ≤ ∑ s ∈ topsOn X p t0, al L a s` using `Finset.sum_nonneg (fun s hs => (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)).2.2.2.1)`. Establish `h0 : 0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s` using `mul_nonneg hg hsum`. Establish `hg0` using `g_zero_le_gamma_sum P X K hK a b hW p hp j hj t0`. Establish `hgU` using `gU_le P X K hK a b hW p hp j hj t0`.

Establish `hPr` using `Pr_nonneg P X K hK b p j hj t0`. Establish `hm : max (g0 X K a b p j t0) 0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s` using `max_le hg0 h0`. Conclude with `⟨hm, max_le (by linarith) hm⟩`.
-/
theorem orbit_max_le (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (a b : HH D → ℤ) (hW : InWin L a b)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t0 : HH D) :
    max (g0 X K a b p j t0) 0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s ∧
    max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0) ≤
      gam p * ∑ s ∈ topsOn X p t0, al L a s := by
  have hg := (gam_facts p hp).1
  have hsum : 0 ≤ ∑ s ∈ topsOn X p t0, al L a s :=
    Finset.sum_nonneg (fun s hs => (a_bounds P a b hW s (mem_TT_of_topsOn X p t0 s hs)).2.2.2.1)
  have h0 : 0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := mul_nonneg hg hsum
  have hg0 := g_zero_le_gamma_sum P X K hK a b hW p hp j hj t0
  have hgU := gU_le P X K hK a b hW p hp j hj t0
  have hPr := Pr_nonneg P X K hK b p j hj t0
  have hm : max (g0 X K a b p j t0) 0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := max_le hg0 h0
  exact ⟨hm, max_le (by linarith) hm⟩

/- English proof (translation)
Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `ha : 0 ≤ L.sc.a` using `le_trans zero_le_one (sc_one_lt_a L.sc).le`. Establish `hT : (0 : ℝ) ≤ (D.host.TT.card : ℝ)` using `Nat.cast_nonneg _`. Establish `hR : 0 ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)` using `by positivity`. Unfold `gainP`.

Use `split_ifs with hc`. Conclude with `⟨le_rfl, hR⟩`. Prove the components needed by the constructor for the conclusion. Conclude with `add_nonneg (Finset.sum_nonneg (fun t0 _ => le_max_of_le_right (le_max_right _ _))) (Finset.sum_nonneg (fun t0 _ => le_max_right _ _))`. Establish `h1 : ∑ t0 ∈ VV X K a b p, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0) ≤ ∑ t0 ∈ VV X K a b p, gam p * ∑ s ∈ topsOn X p t0, al L a s` using `Finset.sum_le_sum (fun t0 _ => (orbit_max_le P X K hK a b hW p hp j hj t0).2)`.

Establish `h2 : ∑ t0 ∈ reps X p \ VV X K a b p, max (g0 X K a b p j t0) 0 ≤ ∑ t0 ∈ reps X p \ VV X K a b p, gam p * ∑ s ∈ topsOn X p t0, al L a s` using `Finset.sum_le_sum (fun t0 _ => (orbit_max_le P X K hK a b hW p hp j hj t0).1)`. Establish `h3` using `Finset.sum_sdiff (VV_subset_reps X K a b p) (f := fun t0 => gam p * ∑ s ∈ topsOn X p t0, al L a s)`. Establish `h3' : ∑ t0 ∈ reps X p, gam p * ∑ s ∈ topsOn X p t0, al L a s = gam p * ∑ s ∈ D.host.TT, al L a s`. Rewrite using `[← Finset.mul_sum, sum_reps]`. Rewrite `h3` using `[h3']`.

Establish `h4 : ∑ s ∈ D.host.TT, al L a s ≤ (D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `Finset.sum_le_card_nsmul _ _ _ (fun s hs => (a_bounds P a b hW s hs).2.2.2.2)`. Take `⟨hg0, hg1⟩` from `gam_facts p hp`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 hg0`.

Establish `h6 : gam p * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)) ≤ 4 / 3 * (1 / p) * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a))` using `mul_le_mul_of_nonneg_right hg1 (by positivity)`. Establish `h7 : 4 / 3 * (1 / (p : ℝ)) * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)) = 2 / 5 * (4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gain_bounds (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (a b : HH D → ℤ) (hW : InWin L a b)
    (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    0 ≤ gainP X K a b p j ∧ gainP X K a b p j ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ha : 0 ≤ L.sc.a := le_trans zero_le_one (sc_one_lt_a L.sc).le
  have hT : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hR : 0 ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ) := by positivity
  unfold gainP
  split_ifs with hc
  · exact ⟨le_rfl, hR⟩
  · constructor
    · exact add_nonneg (Finset.sum_nonneg (fun t0 _ => le_max_of_le_right (le_max_right _ _)))
        (Finset.sum_nonneg (fun t0 _ => le_max_right _ _))
    · have h1 : ∑ t0 ∈ VV X K a b p, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0) ≤
          ∑ t0 ∈ VV X K a b p, gam p * ∑ s ∈ topsOn X p t0, al L a s :=
        Finset.sum_le_sum (fun t0 _ => (orbit_max_le P X K hK a b hW p hp j hj t0).2)
      have h2 : ∑ t0 ∈ reps X p \ VV X K a b p, max (g0 X K a b p j t0) 0 ≤
          ∑ t0 ∈ reps X p \ VV X K a b p, gam p * ∑ s ∈ topsOn X p t0, al L a s :=
        Finset.sum_le_sum (fun t0 _ => (orbit_max_le P X K hK a b hW p hp j hj t0).1)
      have h3 := Finset.sum_sdiff (VV_subset_reps X K a b p) (f := fun t0 => gam p * ∑ s ∈ topsOn X p t0, al L a s)
      have h3' : ∑ t0 ∈ reps X p, gam p * ∑ s ∈ topsOn X p t0, al L a s = gam p * ∑ s ∈ D.host.TT, al L a s := by
        rw [← Finset.mul_sum, sum_reps]
      rw [h3'] at h3
      have h4 : ∑ s ∈ D.host.TT, al L a s ≤ (D.host.TT.card : ℝ) * (6 / 5 * L.sc.a) := by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ (fun s hs => (a_bounds P a b hW s hs).2.2.2.2)
      obtain ⟨hg0, hg1⟩ := gam_facts p hp
      have h5 := mul_le_mul_of_nonneg_left h4 hg0
      have h6 : gam p * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)) ≤
          4 / 3 * (1 / p) * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)) :=
        mul_le_mul_of_nonneg_right hg1 (by positivity)
      have h7 : 4 / 3 * (1 / (p : ℝ)) * ((D.host.TT.card : ℝ) * (6 / 5 * L.sc.a)) =
          2 / 5 * (4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)) := by
        field_simp
        ring
      linarith

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `hW s hs`. Establish `ha2` using `two_le_a L.sc`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hX1 : 1 < L.sc.X'`. Unfold `Scale.X'`.

Establish `hpos : 0 < L.sc.x ^ (L.sc.eps / 3)` using `Real.rpow_pos_of_pos (by linarith) _`. Use `Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : 0 < L.sc.X'` using `by linarith`. Establish `hpe : L.sc.X' ≤ (p : ℝ) ^ e`.

Combine the equalities or inequalities in the displayed calculation. Establish `has : 0 ≤ (a s : ℝ)` using `by linarith`. Establish `hb'0 : 0 ≤ L.sc.b'`. Unfold `Scale.b'`. Conclude with `div_nonneg (by linarith) hX0.le`.

Use `set Q : ℝ := (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) with hQ`. Establish `hQx : L.sc.b' / Q ≤ L.sc.b' / L.sc.x`. Break down `Nat.eq_zero_or_pos D.R.k with hk | hk` into its components or cases. Establish `hQ0 : Q = 0` using `by rw [hQ, hk]; simp`. Rewrite using `[hQ0, div_zero]`.

Conclude with `div_nonneg hb'0 (by linarith)`. Establish `hk1 : (1 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk`. Establish `hxA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hxQ : L.sc.x ≤ Q`.

Rewrite using `[hQ]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hk1) (show (0 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) by linarith)]`. Conclude with `div_le_div_of_nonneg_left hb'0 (by linarith) hxQ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem top_small (a b : HH D → ℤ) (hW : InWin L a b) (p : ℕ) (hp : p.Prime) (hpX : L.sc.X' ≤ (p : ℝ))
    (s : HH D) (hs : s ∈ D.host.TT) (e : ℕ) (he : 1 ≤ e) :
    (a s : ℝ) / (p : ℝ) ^ e ≤ L.sc.b' + L.sc.b' / L.sc.x := by
  obtain ⟨h1, h2, -⟩ := hW s hs
  have ha2 := two_le_a L.sc
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hX1 : 1 < L.sc.X' := by
    unfold Scale.X'
    have hpos : 0 < L.sc.x ^ (L.sc.eps / 3) := Real.rpow_pos_of_pos (by linarith) _
    have := Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))
    linarith
  have hX0 : 0 < L.sc.X' := by linarith
  have hpe : L.sc.X' ≤ (p : ℝ) ^ e := by
    calc L.sc.X' ≤ (p : ℝ) := hpX
      _ = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he
  have has : 0 ≤ (a s : ℝ) := by linarith
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b'
    exact div_nonneg (by linarith) hX0.le
  set Q : ℝ := (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) with hQ
  have hQx : L.sc.b' / Q ≤ L.sc.b' / L.sc.x := by
    rcases Nat.eq_zero_or_pos D.R.k with hk | hk
    · have hQ0 : Q = 0 := by rw [hQ, hk]; simp
      rw [hQ0, div_zero]
      exact div_nonneg hb'0 (by linarith)
    · have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
      have hxA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2) := by
        calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ L.sc.x ^ (Scale.A / 2) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le (by unfold Scale.A; norm_num)
      have hxQ : L.sc.x ≤ Q := by
        rw [hQ]
        nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (show (0 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) by linarith)]
      exact div_le_div_of_nonneg_left hb'0 (by linarith) hxQ
  calc (a s : ℝ) / (p : ℝ) ^ e ≤ (a s : ℝ) / L.sc.X' := div_le_div_of_nonneg_left has hX0 hpe
    _ ≤ (L.sc.a + L.sc.a / Q) / L.sc.X' := div_le_div_of_nonneg_right h2 hX0.le
    _ = L.sc.b' + L.sc.b' / Q := by unfold Scale.b'; ring
    _ ≤ L.sc.b' + L.sc.b' / L.sc.x := by linarith

/- English proof (translation)
Take `⟨he, s', hs', -, -, hpart, -⟩` from `hx`. Establish `hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)` using `fun t ht => (hW t ht).2.2`. Rewrite using `[hpart]`. Conclude with `le_trans (top_small a b hW p hp hpX s hs e he.pos) (fill_top_ge X b hb j s' hs')`.
-/
theorem excl_small_of_ge (X : Inst D L) (a b : HH D → ℤ) (hW : InWin L a b) (p : ℕ) (hp : p.Prime)
    (hpX : L.sc.X' ≤ (p : ℝ)) (j : ℕ) (s : HH D) (hs : s ∈ D.host.TT) (e : ℕ) (hx : Excl D p s e) :
    (a s : ℝ) / (p : ℝ) ^ e ≤ fill X b j (partner D p s e) := by
  obtain ⟨he, s', hs', -, -, hpart, -⟩ := hx
  have hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (hW t ht).2.2
  rw [hpart]
  exact le_trans (top_small a b hW p hp hpX s hs e he.pos) (fill_top_ge X b hb j s' hs')

/- English proof (translation)
Introduce and unpack `⟨he, s', _, _, _, hpart, _⟩`. Unfold `partner at hpart`. Establish `h1` using `congrArg Prod.fst hpart`. Simplify using `[hsg, he] at h1`.
-/
theorem not_excl_of_sg (p : ℕ) (hsg : IsSg D p) (s : HH D) (e : ℕ) : ¬ Excl D p s e := by
  rintro ⟨he, s', _, _, _, hpart, _⟩
  unfold partner at hpart
  have h1 := congrArg Prod.fst hpart
  simp [hsg, he] at h1

/- English proof (translation)
Introduce `hs`. Establish `e : PrimeClass.inertClass = PrimeClass.signal` using `(show D.host.cls p = PrimeClass.inertClass from h).symm.trans hs`. Consider the cases of `e`.
-/
theorem not_singular_of_central (p : ℕ) (h : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro hs
  have e : PrimeClass.inertClass = PrimeClass.signal :=
    (show D.host.cls p = PrimeClass.inertClass from h).symm.trans hs
  cases e

/- English proof (translation)
Unfold `askP`. Establish `hns : ¬ IsSg D p` using `not_singular_of_central p hc0`. Establish `hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)` using `fun t ht => (hW t ht).2.2`. Establish `hterm : ∀ e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - fill X b j (partner D p s e)) else 0) = 0`. Introduce `e`.

Use `split_ifs with he`. Establish `hpart : partner D p s e = (false, s)`. Unfold `partner`. Simplify using `[hns, hh]`. Rewrite using `[hpart]`.

Establish `h1` using `top_small a b hW p hp hpX s hs e he.pos`. Establish `h2` using `fill_top_ge X b hb j s hs`. Conclude with `max_eq_left (by linarith)`. Both sides reduce to the same expression. Simplify using `only [hterm, tsum_zero]`.
-/
theorem hypothesis₂ (X : Inst D L) (a b : HH D → ℤ) (hW : InWin L a b) (p : ℕ) (hp : p.Prime)
    (hpX : L.sc.X' ≤ (p : ℝ)) (hc0 : IsResidueClassZero D p) (hh : hP D p = 0) (j : ℕ) (s : HH D) (hs : s ∈ D.host.TT) :
    askP X a b p j s = 0 := by
  unfold askP
  have hns : ¬ IsSg D p := not_singular_of_central p hc0
  have hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (hW t ht).2.2
  have hterm : ∀ e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - fill X b j (partner D p s e)) else 0)
      = 0 := by
    intro e
    split_ifs with he
    · have hpart : partner D p s e = (false, s) := by
        unfold partner
        simp [hns, hh]
      rw [hpart]
      have h1 := top_small a b hW p hp hpX s hs e he.pos
      have h2 := fill_top_ge X b hb j s hs
      exact max_eq_left (by linarith)
    · rfl
  simp only [hterm, tsum_zero]

/- English proof (translation)
Unfold `topsOn`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`.

Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem sum_TTP_served (X : Inst D L) (V : Finset (HH D)) (p : ℕ) (f : HH D → ℝ) :
    ∑ s ∈ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ V), f s = ∑ t0 ∈ V, ∑ s ∈ topsOn X p t0, f s := by
  unfold topsOn
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_ite_eq]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `hc.2.2.2.1`. Rewrite `h1` using `[h0, addOrderOf_zero]`. Establish `he : 0 < L.sc.eps / 4` using `div_pos L.sc.eps_pos (by norm_num)`. Establish `h2 : 1 < L.sc.x ^ (L.sc.eps / 4)` using `Real.one_lt_rpow L.sc.one_lt_alt he`.

Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hP_ne_zero_of_cand (K : Consts) (p : ℕ) (hc : Cand D L K p) : hP D p ≠ 0 := by
  intro h0
  have h1 := hc.2.2.2.1
  rw [h0, addOrderOf_zero] at h1
  have he : 0 < L.sc.eps / 4 := div_pos L.sc.eps_pos (by norm_num)
  have h2 : 1 < L.sc.x ^ (L.sc.eps / 4) := Real.one_lt_rpow L.sc.one_lt_alt he
  push_cast at h1
  linarith

/- English proof (translation)
Introduce `p hp hcl hpX''`. Use `⟨fun j hj => gain_bounds P X K hK a b hW p hp j hj, ?_⟩` and prove the remaining obligations. Establish `hC0 : 0 ≤ C` using `le_trans (by norm_num) hN.C3`. Establish `hfl0` using `fl_nonneg (D := D) L.sc C hC0 p hp`. Establish `hm0 : (0 : ℝ) ≤ (D.R.m : ℝ)` using `Nat.cast_nonneg _`.

Establish `hm1 : (1 : ℝ) ≤ (D.R.m : ℝ)`. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.m)` after adjusting the coercions. Establish `hgain0 : 0 ≤ ∑ j ∈ SizeData₂.lifts D, gainP X K a b p j` using `Finset.sum_nonneg (fun j hj => (gain_bounds P X K hK a b hW p hp j hj).1)`. Distinguish the cases in `hVV : VV X K a b p = ∅`.

Establish `htau : tauP X K a b p = 0` using `by unfold tauP; rw [if_pos hVV]`. Rewrite using `[htau, sub_zero]`. Distinguish the cases in `hfull : IsSg D p ∨ L.sc.X' ≤ (p : ℝ)`. Establish `hTTP : TTP X K a b p = D.host.TT` using `by unfold TTP; rw [if_pos hfull]`. Rewrite using `[hTTP]`.

Distinguish the cases in `hc : IsResidueClassZero D p ∧ hP D p = 0`. Establish `hpX : L.sc.X' ≤ (p : ℝ)` using `hfull.resolve_left (not_singular_of_central p hc.1)`. Establish `hlo` using `lo_nonneg P K hK Ce C bo hN p hp`. Establish `h1 : ∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, (askP X a b p j s - lo K L C bo p) ≤ 0`. Apply `Finset.sum_nonpos` to reduce the goal to its premises.

Introduce `j _`. Apply `Finset.sum_nonpos` to reduce the goal to its premises. Introduce `s hs`. Rewrite using `[hypothesis₂ X a b hW p hp hpX hc.1 hc.2 j s hs]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2` using `mul_nonneg hm0 hfl0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg : ∀ j, gainP X K a b p j = ∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0`. Introduce `j`. Unfold `gainP`.

Rewrite using `[if_neg (fun h => h.elim hc (fun h' => absurd hpX'' (not_le.2 h'))), hVV]`. Simplify using the standard rewrite rules. Simplify using `only [hg]`. Apply `noop P X K hK Ce C bo hCe hN a b hW p hp (h9 p hp hpX'')` to reduce the goal to its premises. Introduce `j _ s hs e hx`.

Break down `hfull with hsg | hpX` into its components or cases. Conclude with `absurd hx (not_excl_of_sg p hsg s e)`. Conclude with `excl_small_of_ge X a b hW p hp hpX j s hs e hx`. Establish `hTTP : TTP X K a b p = ∅`. Unfold `TTP`.

Rewrite using `[if_neg hfull, hVV]`. Simplify using the standard rewrite rules. Rewrite using `[hTTP]`. Simplify using `only [Finset.sum_empty, Finset.sum_const_zero]`. Establish `h2` using `mul_nonneg hm0 hfl0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc` using `cand_of_VV_ne X K a b p hVV`. Establish `hV : VV X K a b p = goodReps X p`. Assume the negation of the conclusion as `hne`. Apply `hVV` to reduce the goal to its premises.

Unfold `VV at hne ⊢`. Use `split_ifs at hne ⊢ with h`. Conclude with `absurd rfl hne`. Both sides reduce to the same expression. Establish `hnfull : ¬ (IsSg D p ∨ L.sc.X' ≤ (p : ℝ))`.

Introduce and unpack `(h | h)`. Conclude with `not_singular_of_central p hc.2.2.1 h`. Conclude with `absurd hc.2.1 (not_lt.2 h)`. Establish `hTTP : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ VV X K a b p)`. Unfold `TTP`.

Rewrite using `[if_neg hnfull]`. Use `set V := VV X K a b p with hVdef`. Establish `htau : tauP X K a b p = (X.ep p : ℝ) + (D.R.m : ℝ) * ∑ t0 ∈ V, ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1)`. Unfold `tauP`. Rewrite using `[if_neg hVV, Finset.mul_sum]`.

Establish `hgain : ∀ j ∈ SizeData₂.lifts D, ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) ≤ gainP X K a b p j`. Introduce `j _`. Unfold `gainP`. Rewrite using `[if_neg (fun h => h.elim (fun h' => hP_ne_zero_of_cand K p hc h'.2) (fun h' => absurd hpX'' (not_le.2 h')))]`. Establish `h1 : ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) ≤ ∑ t0 ∈ V, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0)` using `Finset.sum_le_sum (fun t0 _ => le_max_left _ _)`.

Establish `h2 : 0 ≤ ∑ t0 ∈ reps X p \ V, max (g0 X K a b p j t0) 0` using `Finset.sum_nonneg (fun t0 _ => le_max_right _ _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstar : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askP X a b p j s - lo K L C bo p) ≤ ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) + (∑ t0 ∈ V, dl X K p t0 - ∑ t0 ∈ V, ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1))`. Introduce `j hj`. Rewrite using `[hTTP, sum_TTP_served, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t0 ht0`. Use `hStar p hc t0 (by rw [← hV]; exact ht0) j hj` as an intermediate fact. Unfold `StarAt at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `Finset.sum_le_sum hstar`. Rewrite `h1` using `[Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_lifts]`. Establish `h2` using `Finset.sum_le_sum hgain`. Establish `h3` using `sum_dl_add_ep_le X K hK Ce C bo hCe hN p hp (h9 p hp hpX'')`. Establish `h4 : ∑ t0 ∈ V, dl X K p t0 ≤ ∑ t0 ∈ reps X p, dl X K p t0` using `Finset.sum_le_sum_of_subset_of_nonneg (VV_subset_reps X K a b p) (fun t0 _ _ => dl_nonneg X K hK p hp t0)`.

Establish `hep : (0 : ℝ) ≤ (X.ep p : ℝ)` using `Nat.cast_nonneg _`. Establish `h5 : (X.ep p : ℝ) + (D.R.m : ℝ) * ∑ t0 ∈ V, dl X K p t0 ≤ (D.R.m : ℝ) * fl D L.sc C p`. Establish `h6 : (D.R.m : ℝ) * (∑ t0 ∈ V, dl X K p t0 + (X.ep p : ℝ)) ≤ (D.R.m : ℝ) * fl D L.sc C p` using `mul_le_mul_of_nonneg_left (by linarith) hm0`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[htau]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gain_bound_at_of_star (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hCe : 0 ≤ Ce)
    (hN : GainBoundConstants K Ce C bo)
    (h9 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ L.sc.X'' D.R.n →
      (X.ep p : ℝ) ≤ Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a)
    (a b : HH D → ℤ) (hW : InWin L a b)
    (hStar : ∀ p, Cand D L K p → ∀ t0 ∈ goodReps X p, ∀ j ∈ SizeData₂.lifts D, StarAt X K C bo a b p j t0) :
    GainBoundAtPairUniform X K C bo a b := by
  intro p hp hcl hpX''
  refine ⟨fun j hj => gain_bounds P X K hK a b hW p hp j hj, ?_⟩
  have hC0 : 0 ≤ C := le_trans (by norm_num) hN.C3
  have hfl0 := fl_nonneg (D := D) L.sc C hC0 p hp
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hgain0 : 0 ≤ ∑ j ∈ SizeData₂.lifts D, gainP X K a b p j :=
    Finset.sum_nonneg (fun j hj => (gain_bounds P X K hK a b hW p hp j hj).1)
  by_cases hVV : VV X K a b p = ∅
  · have htau : tauP X K a b p = 0 := by unfold tauP; rw [if_pos hVV]
    rw [htau, sub_zero]
    by_cases hfull : IsSg D p ∨ L.sc.X' ≤ (p : ℝ)
    · have hTTP : TTP X K a b p = D.host.TT := by unfold TTP; rw [if_pos hfull]
      rw [hTTP]
      by_cases hc : IsResidueClassZero D p ∧ hP D p = 0
      ·
        have hpX : L.sc.X' ≤ (p : ℝ) := hfull.resolve_left (not_singular_of_central p hc.1)
        have hlo := lo_nonneg P K hK Ce C bo hN p hp
        have h1 : ∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, (askP X a b p j s - lo K L C bo p) ≤ 0 := by
          apply Finset.sum_nonpos
          intro j _
          apply Finset.sum_nonpos
          intro s hs
          rw [hypothesis₂ X a b hW p hp hpX hc.1 hc.2 j s hs]
          linarith
        have h2 := mul_nonneg hm0 hfl0
        linarith
      ·
        have hg : ∀ j, gainP X K a b p j = ∑ t0 ∈ reps X p, max (g0 X K a b p j t0) 0 := by
          intro j
          unfold gainP
          rw [if_neg (fun h => h.elim hc (fun h' => absurd hpX'' (not_le.2 h'))), hVV]
          simp
        simp only [hg]
        apply noop P X K hK Ce C bo hCe hN a b hW p hp (h9 p hp hpX'')
        intro j _ s hs e hx
        rcases hfull with hsg | hpX
        · exact absurd hx (not_excl_of_sg p hsg s e)
        · exact excl_small_of_ge X a b hW p hp hpX j s hs e hx
    ·
      have hTTP : TTP X K a b p = ∅ := by
        unfold TTP
        rw [if_neg hfull, hVV]
        simp
      rw [hTTP]
      simp only [Finset.sum_empty, Finset.sum_const_zero]
      have h2 := mul_nonneg hm0 hfl0
      linarith
  ·
    have hc := cand_of_VV_ne X K a b p hVV
    have hV : VV X K a b p = goodReps X p := by
      by_contra hne
      apply hVV
      unfold VV at hne ⊢
      split_ifs at hne ⊢ with h
      · exact absurd rfl hne
      · rfl
    have hnfull : ¬ (IsSg D p ∨ L.sc.X' ≤ (p : ℝ)) := by
      rintro (h | h)
      · exact not_singular_of_central p hc.2.2.1 h
      · exact absurd hc.2.1 (not_lt.2 h)
    have hTTP : TTP X K a b p = D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ VV X K a b p) := by
      unfold TTP; rw [if_neg hnfull]
    set V := VV X K a b p with hVdef
    have htau : tauP X K a b p = (X.ep p : ℝ) + (D.R.m : ℝ) * ∑ t0 ∈ V,
        ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1) := by
      unfold tauP
      rw [if_neg hVV, Finset.mul_sum]
    have hgain : ∀ j ∈ SizeData₂.lifts D, ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) ≤ gainP X K a b p j := by
      intro j _
      unfold gainP
      rw [if_neg (fun h => h.elim (fun h' => hP_ne_zero_of_cand K p hc h'.2) (fun h' => absurd hpX'' (not_le.2 h')))]
      have h1 : ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) ≤
          ∑ t0 ∈ V, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0) :=
        Finset.sum_le_sum (fun t0 _ => le_max_left _ _)
      have h2 : 0 ≤ ∑ t0 ∈ reps X p \ V, max (g0 X K a b p j t0) 0 :=
        Finset.sum_nonneg (fun t0 _ => le_max_right _ _)
      linarith
    have hstar : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askP X a b p j s - lo K L C bo p) ≤
        ∑ t0 ∈ V, (gU X K a b p j t0 - Pr X K b p j t0) + (∑ t0 ∈ V, dl X K p t0 -
          ∑ t0 ∈ V, ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1)) := by
      intro j hj
      rw [hTTP, sum_TTP_served, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t0 ht0
      have := hStar p hc t0 (by rw [← hV]; exact ht0) j hj
      unfold StarAt at this
      linarith
    have h1 := Finset.sum_le_sum hstar
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_lifts] at h1
    have h2 := Finset.sum_le_sum hgain
    have h3 := sum_dl_add_ep_le X K hK Ce C bo hCe hN p hp (h9 p hp hpX'')
    have h4 : ∑ t0 ∈ V, dl X K p t0 ≤ ∑ t0 ∈ reps X p, dl X K p t0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (VV_subset_reps X K a b p) (fun t0 _ _ => dl_nonneg X K hK p hp t0)
    have hep : (0 : ℝ) ≤ (X.ep p : ℝ) := Nat.cast_nonneg _
    have h5 : (X.ep p : ℝ) + (D.R.m : ℝ) * ∑ t0 ∈ V, dl X K p t0 ≤ (D.R.m : ℝ) * fl D L.sc C p := by
      have h6 : (D.R.m : ℝ) * (∑ t0 ∈ V, dl X K p t0 + (X.ep p : ℝ)) ≤ (D.R.m : ℝ) * fl D L.sc C p :=
        mul_le_mul_of_nonneg_left (by linarith) hm0
      nlinarith
    rw [htau]
    nlinarith

/- English proof (translation)
Establish `hXa : L.sc.X'' D.R.n ≤ L.sc.a`. Take `⟨_, _, _, hw500, _⟩` from `basics P`. Unfold `Scale.X''`. Conclude with `div_le_self (le_trans zero_le_one (sc_one_lt_a L.sc).le) (by linarith)`. Conclude with `fun a b hW => gain_bound_at_of_star P X K hK (Ce + 1) C bo (by linarith) hN (fun p hp hpX => h9.1 p hp (le_trans hpX hXa)) a b hW (fun p hc t0 ht0 j hj => hStar a b hW p hc t0 ht0 j hj)`.
-/
theorem gain_bound_all_of_star (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (hK : K.Nonneg) (Ce C bo : ℝ) (hCe : 0 ≤ Ce)
    (hN : GainBoundConstants K (Ce + 1) C bo) (h9 : adm9 D L X Ce) (hStar : StarAll X K C bo) : GainBoundAllUniform X K C bo := by
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := by
    obtain ⟨_, _, _, hw500, _⟩ := basics P
    unfold Scale.X''
    exact div_le_self (le_trans zero_le_one (sc_one_lt_a L.sc).le) (by linarith)
  exact fun a b hW => gain_bound_at_of_star P X K hK (Ce + 1) C bo (by linarith) hN
    (fun p hp hpX => h9.1 p hp (le_trans hpX hXa)) a b hW (fun p hc t0 ht0 j hj => hStar a b hW p hc t0 ht0 j hj)

end Formalism.MainNotions.AuxBlock8.Pf

end
