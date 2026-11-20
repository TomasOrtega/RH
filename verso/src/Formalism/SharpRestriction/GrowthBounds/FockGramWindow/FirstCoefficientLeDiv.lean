import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.RestWinOfLvl

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

/- English proof (translation)
Unfold `segG`. Use `split_ifs with h`. Conclude with `(segStart TT j).pos`. Conclude with `Nat.one_le_iff_ne_zero.mpr h`.
-/
theorem segG_pos {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : 1 ≤ segG TT j := by
  unfold segG
  split_ifs with h
  · exact (segStart TT j).pos
  · exact Nat.one_le_iff_ne_zero.mpr h

/- English proof (translation)
Unfold `cap`. Use `push_cast`. Use `add_le_add le_rfl ((Finset.sum_le_card_nsmul _ _ B ?_).trans ?_)` and prove the remaining obligations. Introduce `i _`. Establish `hc : coarseA p S b i ≤ S.bTop i`.

Unfold `coarseA`. Conclude with `(Nat.div_le_self _ _).trans (Nat.sub_le _ _)`. Establish `hcR : (coarseA p S b i : ℝ) ≤ B` using `(Nat.cast_le.mpr hc).trans (hB i)`. Establish `h0 : (0 : ℝ) ≤ B` using `(Nat.cast_nonneg _).trans (hB i)`. Establish `hoe : (0 : ℝ) ≤ (oEff S b i : ℝ)` using `Nat.cast_nonneg _`.

Apply the tactic sequence `split_ifs <;> linarith`. Simplify using the standard rewrite rules.
-/
theorem cap_le' {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B) (l : ℕ) :
    (cap p S b l : ℝ) ≤ S.A0 p + s * B := by
  unfold cap
  push_cast
  refine add_le_add le_rfl ((Finset.sum_le_card_nsmul _ _ B ?_).trans ?_)
  · intro i _
    have hc : coarseA p S b i ≤ S.bTop i := by
      unfold coarseA
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hcR : (coarseA p S b i : ℝ) ≤ B := (Nat.cast_le.mpr hc).trans (hB i)
    have h0 : (0 : ℝ) ≤ B := (Nat.cast_nonneg _).trans (hB i)
    have hoe : (0 : ℝ) ≤ (oEff S b i : ℝ) := Nat.cast_nonneg _
    split_ifs <;> linarith
  · simp

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

/- English proof (translation)
Unfold `SegData.A0`. Use `(Int.floor_le _).trans ?_` and prove the remaining obligations. Establish `hp25` using `p25 hS.hF`. Establish `hp1 : 1 ≤ X.p` using `X.std.1.prime.one_lt.le`. Establish `hQ : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ)` using `by show (X.p : ℝ) ≤ ((X.p ^ segG X.L.TT X.j : ℕ) : ℝ)`.

Establish `: X.p ^ 1 ≤ X.p ^ segG X.L.TT X.j` using `Nat.pow_le_pow_right hp1 (segG_pos _ _)`. Rewrite `this` using `[pow_one]`. Conclude with `this` after adjusting the coercions. Establish `hQ25 : (25 : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ)` using `hp25.trans hQ`. Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`.

Establish `hE` using `hS.E0`. Establish `ha : (((X.S C0 CE1 CE2).a : ℕ) : ℝ) = X.L.a` using `rfl`. Rewrite using `[ha, div_le_div_iff₀ (by linarith) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem first_coefficient_le_div : (((X.S C0 CE1 CE2).A0 X.p : ℤ) : ℝ) ≤ X.L.a / 25 := by
  unfold SegData.A0
  refine (Int.floor_le _).trans ?_
  have hp25 := p25 hS.hF
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hQ : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := by
    show (X.p : ℝ) ≤ ((X.p ^ segG X.L.TT X.j : ℕ) : ℝ)
    have : X.p ^ 1 ≤ X.p ^ segG X.L.TT X.j := Nat.pow_le_pow_right hp1 (segG_pos _ _)
    rw [pow_one] at this
    exact_mod_cast this
  have hQ25 : (25 : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := hp25.trans hQ
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hE := hS.E0
  have ha : (((X.S C0 CE1 CE2).a : ℕ) : ℝ) = X.L.a := rfl
  rw [ha, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `div_nonneg (by linarith) (by linarith)`. Consider the case `succ n`.

Establish `hA` using `Fin.sum_univ_castSucc f`. Establish `hB` using `Fin.sum_univ_succ f`. Establish `hC : ∑ i : Fin n, p * f i.castSucc ≤ ∑ i : Fin n, f i.succ` using `Finset.sum_le_sum (fun i _ => hs _ _ Fin.castSucc_lt_succ)`. Rewrite `hC` using `[← Finset.mul_sum]`. Establish `hf0` using `h0 0`.

Establish `hfl` using `h1 (Fin.last n)`. Rewrite using `[le_div_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem geo_lemma (n : ℕ) (p : ℝ) (hp : 1 < p) (f : Fin n → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∀ i, f i ≤ 1) (hs : ∀ i j : Fin n, i < j → p * f i ≤ f j) : ∑ i, f i ≤ p / (p - 1) := by
  cases n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg (by linarith) (by linarith)
  | succ n =>
    have hA := Fin.sum_univ_castSucc f
    have hB := Fin.sum_univ_succ f
    have hC : ∑ i : Fin n, p * f i.castSucc ≤ ∑ i : Fin n, f i.succ :=
      Finset.sum_le_sum (fun i _ => hs _ _ Fin.castSucc_lt_succ)
    rw [← Finset.mul_sum] at hC
    have hf0 := h0 0
    have hfl := h1 (Fin.last n)
    rw [le_div_iff₀ (by linarith)]
    nlinarith

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `hK4` using `hK.2.2.2`. Unfold `Oplus at hK4`. Establish `hcap` using `cap_le' (p := X.p) (X.S C0 CE1 CE2) b (5 / 2 * X.L.b') hS.bTop X.s`. Establish `hA0` using `first_coefficient_le_div hS`.

Establish `hm4 : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`. Establish `hpg` using `hF.p_ge`. Establish `hp25 : (25 : ℝ) ≤ (X.L.p : ℝ)` using `by nlinarith`. Establish `hb0` using `hF.b0`. Establish `hkb : ((X.L.m : ℝ) + 1) * X.L.b' ≤ X.L.a / 4` using `hS.kb`.

Establish `hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m` using `by exact_mod_cast hF.s_le`. Establish `hsb : (X.s : ℝ) * X.L.b' ≤ X.L.a / 8` using `by nlinarith`. Establish `hLa0 : 0 ≤ X.L.La C0` using `hF.La0`. Establish `hLa4 : 4 * X.L.La C0 < (X.L.m : ℝ) + 1` using `hS.La4`. Establish `hc1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 4`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : 4 / (X.L.p : ℝ) ^ 2 ≤ 4 / 625` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hq0 : 0 ≤ 4 / (X.L.p : ℝ) ^ 2` using `by positivity`.

Establish `hPpos : ∀ i, (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)` using `fun i => by`. Conclude with `twoPow_pos C0 CE1 CE2 X i` after adjusting the coercions. Establish `hg` using `geo_lemma hS X.s (X.L.p : ℝ) (by linarith) (fun i => 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)) (fun i => (one_div_pos.mpr (hPpos i)).le) (fun i => by`. Use `hS.P1 i` as an intermediate fact. Rewrite using `[div_le_one (hPpos i)]`.

Conclude with `this)` after adjusting the coercions. Use the proof step `(fun i j hij => by`. Establish `h1` using `P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) i j hij`. Establish `h1' : (X.L.p : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) j : ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)`. Conclude with `h1` after adjusting the coercions.

Rewrite using `[mul_one_div, div_le_div_iff₀ (hPpos i) (hPpos j)]`. Use the proof step `linarith)`. Establish `hgeo : (X.L.p : ℝ) / ((X.L.p : ℝ) - 1) ≤ 25 / 24`. Rewrite using `[div_le_div_iff₀ (by linarith) (by norm_num)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hTe : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) = 2 * (X.L.a : ℝ) * ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => by ring)`. Establish `hT0 : 0 ≤ ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)` using `Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hPpos i)).le)`. Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`.

Establish `hT : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ 2 * X.L.a * (25 / 24)`. Rewrite using `[hTe]`. Conclude with `mul_le_mul_of_nonneg_left (hg.trans hgeo) (by positivity)`. Establish `hT0' : 0 ≤ ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)`. Rewrite using `[hTe]`.

Check the signs of the components of the expression. Establish `hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT` using `fun x hx => by`. Unfold `evenTops at hx`. Rewrite `hx` using `[Finset.mem_sort]`. Conclude with `(Finset.mem_filter.mp hx).1`.

Establish `hmem : segNext X.L.TT X.j ∈ X.L.TT`. Unfold `segNext`. Conclude with `hmemT _ (List.get_mem _ _)`. Establish `hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b'` using `hF.bT_le _ hmem`. Establish `hbP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ)` using `Nat.cast_nonneg _`.

Establish `hLb : X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1) ≤ 1 / 4 * ((X.S C0 CE1 CE2).bPlus : ℝ)`. Rewrite using `[mul_div_right_comm]`. Conclude with `mul_le_mul_of_nonneg_right hc1 hbP0`. Establish `hcT : (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2) * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (1 / 4 + 4 / 625) * (2 * X.L.a * (25 / 24))` using `mul_le_mul (by linarith) hT hT0' (by norm_num)`. Establish `hK5 : (b.oPlus : ℝ) ≤ ((cap X.p (X.S C0 CE1 CE2) b X.s : ℤ) : ℝ) + (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2) * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) + X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1)` using `hK4`.

Establish `hfin : (b.oPlus : ℝ) ≤ X.L.a` using `by nlinarith`. Conclude with `hfin` after adjusting the coercions.
-/
theorem oplus_le_a (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    b.oPlus ≤ X.L.a := by
  have hF := hS.hF
  have hK4 := hK.2.2.2
  unfold Oplus at hK4
  have hcap := cap_le' (p := X.p) (X.S C0 CE1 CE2) b (5 / 2 * X.L.b') hS.bTop X.s
  have hA0 := first_coefficient_le_div hS
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpg := hF.p_ge
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith
  have hb0 := hF.b0
  have hkb : ((X.L.m : ℝ) + 1) * X.L.b' ≤ X.L.a / 4 := hS.kb
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hsb : (X.s : ℝ) * X.L.b' ≤ X.L.a / 8 := by nlinarith
  have hLa0 : 0 ≤ X.L.La C0 := hF.La0
  have hLa4 : 4 * X.L.La C0 < (X.L.m : ℝ) + 1 := hS.La4
  have hc1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hq : 4 / (X.L.p : ℝ) ^ 2 ≤ 4 / 625 := by
    gcongr
    nlinarith
  have hq0 : 0 ≤ 4 / (X.L.p : ℝ) ^ 2 := by positivity
  have hPpos : ∀ i, (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := fun i => by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X i
  have hg := geo_lemma hS X.s (X.L.p : ℝ) (by linarith)
    (fun i => 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)) (fun i => (one_div_pos.mpr (hPpos i)).le)
    (fun i => by
      have := hS.P1 i
      rw [div_le_one (hPpos i)]
      exact_mod_cast this)
    (fun i j hij => by
      have h1 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) i j hij
      have h1' : (X.L.p : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) j : ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
        exact_mod_cast h1
      rw [mul_one_div, div_le_div_iff₀ (hPpos i) (hPpos j)]
      linarith)
  have hgeo : (X.L.p : ℝ) / ((X.L.p : ℝ) - 1) ≤ 25 / 24 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hTe : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      = 2 * (X.L.a : ℝ) * ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hT0 : 0 ≤ ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) :=
    Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hPpos i)).le)
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hT : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ 2 * X.L.a * (25 / 24) := by
    rw [hTe]
    exact mul_le_mul_of_nonneg_left (hg.trans hgeo) (by positivity)
  have hT0' : 0 ≤ ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [hTe]
    positivity
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hF.bT_le _ hmem
  have hbP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
  have hLb : X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1)
      ≤ 1 / 4 * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hc1 hbP0
  have hcT : (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
      * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      ≤ (1 / 4 + 4 / 625) * (2 * X.L.a * (25 / 24)) :=
    mul_le_mul (by linarith) hT hT0' (by norm_num)
  have hK5 : (b.oPlus : ℝ) ≤ ((cap X.p (X.S C0 CE1 CE2) b X.s : ℤ) : ℝ)
      + (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
        * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      + X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1) := hK4
  have hfin : (b.oPlus : ℝ) ≤ X.L.a := by nlinarith
  exact_mod_cast hfin

/- English proof (translation)
Unfold `flipOneThree.Inst.winA`. Rewrite using `[Finset.mem_Icc]`. Use `⟨le_rfl, Nat.le_floor ?_⟩` and prove the remaining obligations. Establish `h1 : (0 : ℝ) ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y)`. Establish `hk : (0 : ℝ) ≤ X.L.k` using `by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1`.

Check the signs of the components of the expression. Use `hS.Y1` as an intermediate fact. Check the signs of the components of the expression. Combine the linear relations using `[hS.xa0]`.
-/
theorem a_mem_win : X.L.a ∈ X.winA := by
  unfold flipOneThree.Inst.winA
  rw [Finset.mem_Icc]
  refine ⟨le_rfl, Nat.le_floor ?_⟩
  have h1 : (0 : ℝ) ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y) := by
    have hk : (0 : ℝ) ≤ X.L.k := by
      show (0 : ℝ) ≤ (X.L.m : ℝ) + 1
      positivity
    have := hS.Y1
    positivity
  linarith [hS.xa0]

end Deg

/- English proof (translation)
Establish `hD1 : 0 < D1` using `lt_of_lt_of_le hκ hD`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hYD : 0 < Y * D1` using `mul_pos hY0 hD1`. Establish `hE0 : 0 < E` using `lt_of_lt_of_le hYD hE`. Establish `hq1 : q ≤ 1`.

Establish `: 1 / (2 * Y) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqh : q * h ≤ D1` using `by nlinarith [mul_le_mul_of_nonneg_right hq1 hh0]`.

Establish `hnum : x0l + fl + q * h ≤ 3 * D1` using `by linarith`. Establish `h1 : (x0l + fl + q * h) / E ≤ 3 / Y`. Rewrite using `[div_le_div_iff₀ hE0 hY0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hnum hY0.le]`. Establish `h2 : q ≤ 1 / Y`.

Establish `: 1 / (2 * Y) ≤ 1 / Y` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : 1 / Y + 3 / Y ≤ 5 / Y`. Rewrite using `[← add_div]`.

Use `gcongr`. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eps_num (Y D1 κ q h x0l fl E : ℝ) (hY : 1 ≤ Y) (hκ : 0 < κ) (hD : κ ≤ D1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / (2 * Y))
    (hh0 : 0 ≤ h) (hh : h ≤ κ) (hx : x0l ≤ κ) (hfl : fl ≤ D1) (hE : Y * D1 ≤ E) :
    q + (x0l + fl + q * h) / E ≤ 5 / Y := by
  have hD1 : 0 < D1 := lt_of_lt_of_le hκ hD
  have hY0 : 0 < Y := by linarith
  have hYD : 0 < Y * D1 := mul_pos hY0 hD1
  have hE0 : 0 < E := lt_of_lt_of_le hYD hE
  have hq1 : q ≤ 1 := by
    have : 1 / (2 * Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hqh : q * h ≤ D1 := by nlinarith [mul_le_mul_of_nonneg_right hq1 hh0]
  have hnum : x0l + fl + q * h ≤ 3 * D1 := by linarith
  have h1 : (x0l + fl + q * h) / E ≤ 3 / Y := by
    rw [div_le_div_iff₀ hE0 hY0]
    nlinarith [mul_le_mul_of_nonneg_right hnum hY0.le]
  have h2 : q ≤ 1 / Y := by
    have : 1 / (2 * Y) ≤ 1 / Y := by
      gcongr
      linarith
    linarith
  have h3 : 1 / Y + 3 / Y ≤ 5 / Y := by
    rw [← add_div]
    gcongr
    norm_num
  linarith

end Formalism.MainNotions.G.GramWindowAlt

end
