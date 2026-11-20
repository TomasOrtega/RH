import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SummableAndTsumLeTwoMulDivOfLeDivPow

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Break down `h with ⟨hB, hR⟩ | h` into its components or cases. Establish `h1 : ⌈S⌉ ≤ 0` using `Int.ceil_le.2 (by rw [Int.cast_zero]; linarith)`. Establish `h2 : ((⌈S⌉ : ℤ) : ℝ) ≤ 0` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Int.ceil_lt_add_one S` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ceil_bound (S B R : ℝ) (hSB : S ≤ B) (h : (B = 0 ∧ R = 0) ∨ B + 1 ≤ R) : ((⌈S⌉ : ℤ) : ℝ) ≤ R := by
  rcases h with ⟨hB, hR⟩ | h
  · have h1 : ⌈S⌉ ≤ 0 := Int.ceil_le.2 (by rw [Int.cast_zero]; linarith)
    have h2 : ((⌈S⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  · have := Int.ceil_lt_add_one S
    linarith

/- English proof (translation)
Establish `h2 : 500 ≤ N * q` using `by nlinarith`. Establish `h3 : 1000 ≤ m * (N * q)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fin_arith (m N q : ℝ) (hm : 2 ≤ m) (hN : 1 ≤ N) (hq : 500 ≤ q) :
    m * (8 / 5 * (N * q)) + 1 ≤ 2 * (m * (N * q)) := by
  have h2 : 500 ≤ N * q := by nlinarith
  have h3 : 1000 ≤ m * (N * q) := by nlinarith
  linarith

set_option maxHeartbeats 800000 in
/- English proof (translation)
Take `⟨_, _, _, _, _, _, _, _, _, _, _, hdl1, hdl2, hPr1, hPr2⟩` from `hK`. Take `⟨hk, hN, hSc⟩` from `Nm_le_Sc P`. Establish `hn : 1 ≤ D.R.n` using `D.R.ord_pos`. Take `⟨hw1, hw2⟩` from `w''_le L.sc D.R.n hn`. Establish `hkS` using `P.kS_le`.

Establish `hab` using `two_b'_le_a L.sc`. Establish `hx` using `sc_x_pos L.sc`. Establish `ha` using `sc_one_lt_a L.sc`. Establish `hb'` using `sc_b'_nonneg L.sc`. Establish `hw0` using `sc_w''_nonneg L.sc D.R.n`.

Establish `hη` using `L.etaSz_pos`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `mul_le_mul_of_nonneg_right hk (by linarith)`.

Establish `hw500 : 500 ≤ L.sc.w'' D.R.n` using `by linarith`. Establish `hlg : 0 ≤ Real.logb p (2 * L.sc.a)` using `Real.logb_nonneg hp1 (by linarith)`. Establish `hNm0 : 0 ≤ Nm D` using `by unfold Nm; exact Nat.cast_nonneg _`. Establish `hcG : 0 ≤ cG L` using `by unfold cG; linarith`. Establish `hTT : ∀ s ∈ topsOn X p t0, s ∈ D.host.TT` using `fun s hs => (Finset.mem_filter.1 hs).1`.

Establish `hal : ∀ s ∈ topsOn X p t0, 0 ≤ al L a s ∧ al L a s ≤ 6 / 5 * L.sc.a`. Introduce `s hs`. Take `⟨h2, h3, _⟩` from `h s (hTT s hs)`. Establish `h4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5`. Apply `div_le_div_of_nonneg_left (by linarith) (by norm_num)` to reduce the goal to its premises.

Establish `: 1 ≤ L.sc.x ^ (Scale.A / 2)` using `Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Unfold `al cG`. Apply the tactic sequence `constructor <;> linarith`. Establish `hdl : 0 ≤ dl X K p t0`.

Unfold `dl`. Establish `h1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a)` using `mul_nonneg (mul_nonneg (mul_nonneg hdl1 (Nat.cast_nonneg _)) (by positivity)) hlg`. Establish `h2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2` using `mul_nonneg (mul_nonneg hdl2 (Nat.cast_nonneg _)) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgU : ∀ j ∈ SizeData₂.lifts D, gU X K a b p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s`.

Introduce `j hj`. Unfold `gU`. Use `le_trans (sub_le_self _ hdl) (sub_le_self _ ?_)` and prove the remaining obligations. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `s hs`.

Apply `tsum_nonneg` to reduce the goal to its premises. Introduce `e`. Use `split_ifs`. Apply `le_min` to reduce the goal to its premises. Conclude with `div_nonneg (hal s (Finset.mem_filter.1 hs).1).1 (by positivity)`.

Unfold `capU fillG cG`. Use `fill_ge X b (fun t ht => (h t ht).2.2) j (partner D p s e)` as an intermediate fact. Use `kaJ_le P j hj` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`.

Establish `hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D` using `by linarith`. Establish `hPr : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Pr X K b p j t0`. Introduce `j hj`. Unfold `Pr`. Use `split_ifs with h0`.

Apply `add_nonneg` to reduce the goal to its premises. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `s hs`. Establish `hs'` using `hTT s (Finset.mem_filter.1 hs).1`. Establish `h1 : fill X b j (false, s) = (b s : ℝ) + X.off j (false, s)`.

Unfold `fill`. Rewrite using `[if_pos ⟨rfl, hs'⟩]`. Establish `h2` using `(X.off_top j (false, s) ⟨rfl, hs'⟩).1`. Establish `h3` using `kaJ_le P j hj`. Unfold `fillG`.

Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))`. Establish `hgam : 0 ≤ gam p ∧ gam p * L.sc.a ≤ 4 / 3 * (L.sc.a / p)`.

Establish `hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2` using `by nlinarith`. Establish `hd : (0 : ℝ) < (p : ℝ) ^ 2 - 1` using `by linarith`. Unfold `gam`. Use `⟨div_nonneg hp0.le hd.le, ?_⟩` and prove the remaining obligations. Establish `h1 : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 4 / 3 * (1 / p)`.

Rewrite using `[div_le_iff₀ hd]`. Clear the denominators using the available nonvanishing facts. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L.sc.a)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : ∑ s ∈ topsOn X p t0, al L a s ≤ (Nv X p t0 : ℝ) * (6 / 5 * L.sc.a)`. Unfold `Nv`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hal s hs).2)`. Use `set q : ℝ := L.sc.a / p with hq`.

Establish `hq0 : L.sc.b' ≤ q`. Establish `hX : 0 < L.sc.X'` using `by unfold Scale.X'; exact Real.exp_pos _`. Rewrite using `[hq]`. Unfold `Scale.b'`. Conclude with `div_le_div_of_nonneg_left (by linarith) hp0 hpX.le`.

Establish `hterm : ∀ j ∈ SizeData₂.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤ 8 / 5 * ((Nv X p t0 : ℝ) * q)`. Introduce `j hj`. Establish `hNv : (0 : ℝ) ≤ (Nv X p t0 : ℝ)` using `Nat.cast_nonneg _`. Establish `h1` using `hgU j hj`. Establish `h2` using `hPr j hj`.

Establish `h3 : 0 ≤ max (g0 X K a b p j t0) 0` using `le_max_right _ _`. Establish `h4` using `mul_le_mul_of_nonneg_left hsum hgam.1`. Establish `h5` using `mul_le_mul_of_nonneg_left hgam.2 hNv`. Establish `h6 : 0 ≤ (Nv X p t0 : ℝ) * q` using `mul_nonneg hNv (by linarith)`. Apply `max_le (by linarith)` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `htot : ∑ j ∈ SizeData₂.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤ (D.R.m : ℝ) * (8 / 5 * ((Nv X p t0 : ℝ) * q))`. Establish `h` using `Finset.sum_le_card_nsmul _ _ _ hterm`. Establish `hc : (SizeData₂.lifts D).card = D.R.m` using `by unfold SizeData₂.lifts; simp`. Rewrite `h` using `[hc, nsmul_eq_mul]`.

Conclude with `h`. Establish `hR : 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p = 2 * ((D.R.m : ℝ) * ((Nv X p t0 : ℝ) * q))`. Rewrite using `[hq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hR]`.

Unfold `Sv`. Apply `ceil_bound _ _ _ htot` to reduce the goal to its premises. Break down `Nat.eq_zero_or_pos (Nv X p t0) with h0 | h0` into its components or cases. Use `left`. Establish `h0' : (Nv X p t0 : ℝ) = 0` using `by exact_mod_cast h0`.

Rewrite using `[h0']`. Apply the tactic sequence `constructor <;> ring`. Use `right`. Establish `hm : (2 : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast D.R.two_le_m`. Establish `hNv : (1 : ℝ) ≤ (Nv X p t0 : ℝ)` using `by exact_mod_cast h0`.

Establish `hq500 : 500 ≤ q` using `le_trans hw500 (le_trans hw1 (le_trans hw2 hq0))`. Conclude with `fin_arith _ _ _ hm hNv hq500`.
-/
theorem sv_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ)
    (hp : p.Prime) (hpX : (p : ℝ) < L.sc.X') (t0 : HH D) :
    Sv X K a b p t0 ≤ 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hdl1, hdl2, hPr1, hPr2⟩ := hK
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n hn
  have hkS := P.kS_le
  have hab := two_b'_le_a L.sc
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hb' := sc_b'_nonneg L.sc
  have hw0 := sc_w''_nonneg L.sc D.R.n
  have hη := L.etaSz_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  have hw500 : 500 ≤ L.sc.w'' D.R.n := by linarith
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hTT : ∀ s ∈ topsOn X p t0, s ∈ D.host.TT := fun s hs => (Finset.mem_filter.1 hs).1

  have hal : ∀ s ∈ topsOn X p t0, 0 ≤ al L a s ∧ al L a s ≤ 6 / 5 * L.sc.a := by
    intro s hs
    obtain ⟨h2, h3, _⟩ := h s (hTT s hs)
    have h4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
      have : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
      nlinarith
    unfold al cG
    constructor <;> linarith
  have hdl : 0 ≤ dl X K p t0 := by
    unfold dl
    have h1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) :=
      mul_nonneg (mul_nonneg (mul_nonneg hdl1 (Nat.cast_nonneg _)) (by positivity)) hlg
    have h2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 :=
      mul_nonneg (mul_nonneg hdl2 (Nat.cast_nonneg _)) (by positivity)
    linarith
  have hgU : ∀ j ∈ SizeData₂.lifts D,
      gU X K a b p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L a s := by
    intro j hj
    unfold gU
    refine le_trans (sub_le_self _ hdl) (sub_le_self _ ?_)
    apply Finset.sum_nonneg
    intro s hs
    apply tsum_nonneg
    intro e
    split_ifs
    · apply le_min
      · exact div_nonneg (hal s (Finset.mem_filter.1 hs).1).1 (by positivity)
      · unfold capU fillG cG
        have := fill_ge X b (fun t ht => (h t ht).2.2) j (partner D p s e)
        have := kaJ_le P j hj
        linarith
    · exact le_rfl
  have hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D := by linarith
  have hPr : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Pr X K b p j t0 := by
    intro j hj
    unfold Pr
    split_ifs with h0
    · apply add_nonneg
      · apply Finset.sum_nonneg
        intro s hs
        have hs' := hTT s (Finset.mem_filter.1 hs).1
        have h1 : fill X b j (false, s) = (b s : ℝ) + X.off j (false, s) := by
          unfold fill
          rw [if_pos ⟨rfl, hs'⟩]
        have h2 := (X.off_top j (false, s) ⟨rfl, hs'⟩).1
        have h3 := kaJ_le P j hj
        unfold fillG
        rw [h1]
        linarith
      · exact mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase
    · exact mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))
  have hgam : 0 ≤ gam p ∧ gam p * L.sc.a ≤ 4 / 3 * (L.sc.a / p) := by
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
    unfold gam
    refine ⟨div_nonneg hp0.le hd.le, ?_⟩
    have h1 : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 4 / 3 * (1 / p) := by
      rw [div_le_iff₀ hd]
      field_simp
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L.sc.a)
    calc (p : ℝ) / ((p : ℝ) ^ 2 - 1) * L.sc.a ≤ 4 / 3 * (1 / p) * L.sc.a := h2
      _ = 4 / 3 * (L.sc.a / p) := by ring
  have hsum : ∑ s ∈ topsOn X p t0, al L a s ≤ (Nv X p t0 : ℝ) * (6 / 5 * L.sc.a) := by
    unfold Nv
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hal s hs).2)
  set q : ℝ := L.sc.a / p with hq
  have hq0 : L.sc.b' ≤ q := by
    have hX : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
    rw [hq]
    unfold Scale.b'
    exact div_le_div_of_nonneg_left (by linarith) hp0 hpX.le
  have hterm : ∀ j ∈ SizeData₂.lifts D,
      max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤
        8 / 5 * ((Nv X p t0 : ℝ) * q) := by
    intro j hj
    have hNv : (0 : ℝ) ≤ (Nv X p t0 : ℝ) := Nat.cast_nonneg _
    have h1 := hgU j hj
    have h2 := hPr j hj
    have h3 : 0 ≤ max (g0 X K a b p j t0) 0 := le_max_right _ _
    have h4 := mul_le_mul_of_nonneg_left hsum hgam.1
    have h5 := mul_le_mul_of_nonneg_left hgam.2 hNv
    have h6 : 0 ≤ (Nv X p t0 : ℝ) * q := mul_nonneg hNv (by linarith)
    apply max_le (by linarith)
    nlinarith
  have htot : ∑ j ∈ SizeData₂.lifts D,
      max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0) ≤
        (D.R.m : ℝ) * (8 / 5 * ((Nv X p t0 : ℝ) * q)) := by
    have h := Finset.sum_le_card_nsmul _ _ _ hterm
    have hc : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp
    rw [hc, nsmul_eq_mul] at h
    exact h
  have hR : 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p = 2 * ((D.R.m : ℝ) * ((Nv X p t0 : ℝ) * q)) := by
    rw [hq]; ring
  rw [hR]
  unfold Sv
  apply ceil_bound _ _ _ htot
  rcases Nat.eq_zero_or_pos (Nv X p t0) with h0 | h0
  · left
    have h0' : (Nv X p t0 : ℝ) = 0 := by exact_mod_cast h0
    rw [h0']
    constructor <;> ring
  · right
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    have hNv : (1 : ℝ) ≤ (Nv X p t0 : ℝ) := by exact_mod_cast h0
    have hq500 : 500 ≤ q := le_trans hw500 (le_trans hw1 (le_trans hw2 hq0))
    exact fin_arith _ _ _ hm hNv hq500

def c1 (L : SizeData₂ D) (C : ℝ) : ℝ := C * (cG L + L.etaSz) * Real.log (2 * L.sc.a)
def c2 (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x +
    C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))
def c3 (L : SizeData₂ D) (C bo : ℝ) : ℝ :=
  L.sc.b' / L.sc.x + L.etaSz + C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 + bo
def c4 (K : Consts) (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k + L.sc.a / L.sc.p0 D.R.k)
def cfl (D : D7) (s : Scale) (C : ℝ) : ℝ :=
  C * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log s.a + Real.log s.a ^ 2 / Real.log 2)

/- English proof (translation)
The claim follows from `Real.log_nonneg s.one_lt_alt.le`.
-/
theorem logx_nonneg (s : Scale) : 0 ≤ Real.log s.x := Real.log_nonneg s.one_lt_alt.le

/- English proof (translation)
Unfold `La`. Conclude with `mul_nonneg (mul_nonneg hK (by positivity)) (Real.log_nonneg (sc_one_lt_a s).le)`.
-/
theorem La_nonneg (K : Consts) (hK : 0 ≤ K.La) (s : Scale) : 0 ≤ La K s := by
  unfold La
  exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.log_nonneg (sc_one_lt_a s).le)

/- English proof (translation)
Use `k_ge D` as an intermediate fact. Use `sc_x_pos s` as an intermediate fact. Unfold `Scale.p0`. Check the signs of the components of the expression.
-/
theorem p0_pos (D : D7) (s : Scale) : 0 < s.p0 D.R.k := by
  have := k_ge D
  have := sc_x_pos s
  unfold Scale.p0
  positivity

/- English proof (translation)
Unfold `c3`. Establish `h1 : 0 ≤ L.sc.b' / L.sc.x` using `div_nonneg (sc_b'_nonneg _) (sc_x_pos _).le`. Establish `h2` using `L.etaSz_pos`. Establish `h3 : 0 ≤ C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1` using `div_nonneg (mul_nonneg (mul_nonneg hC (sc_w''_nonneg _ _)) (logx_nonneg _)) (sc_delta1_pos _).le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem third_constant_nonneg (L : SizeData₂ D) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo) : 0 ≤ c3 L C bo := by
  unfold c3
  have h1 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (sc_b'_nonneg _) (sc_x_pos _).le
  have h2 := L.etaSz_pos
  have h3 : 0 ≤ C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
    div_nonneg (mul_nonneg (mul_nonneg hC (sc_w''_nonneg _ _)) (logx_nonneg _)) (sc_delta1_pos _).le
  linarith

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hk` using `k_ge D`. Establish `hx` using `sc_x_pos s`. Establish `hY : 0 < ((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4` using `by positivity`.

Rewrite using `[Real.rpow_neg hp0.le]`. Apply `inv_anti₀ hY` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow_of_exponent_le hp1.le` to reduce the goal to its premises. Unfold `L1`.

Conclude with `Nat.le_ceil _`.
-/
theorem prime_rpow_neg_level_le (D : D7) (s : Scale) (p : ℕ) (hp : p.Prime) :
    (p : ℝ) ^ (-(L1 D s p : ℝ)) ≤ (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hk := k_ge D
  have hx := sc_x_pos s
  have hY : 0 < ((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4 := by positivity
  rw [Real.rpow_neg hp0.le]
  apply inv_anti₀ hY
  calc ((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4 = (p : ℝ) ^ Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4) :=
        (Real.rpow_logb hp0 hp1.ne' hY).symm
    _ ≤ (p : ℝ) ^ (L1 D s p : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hp1.le
        unfold L1
        exact Nat.le_ceil _

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hl : 0 < Real.log p` using `Real.log_pos hp1`. Establish `hk` using `k_ge D`. Establish `hk0 : (0 : ℝ) < D.R.k` using `by linarith`.

Establish `hx` using `sc_x_pos L.sc`. Establish `ha` using `sc_one_lt_a L.sc`. Establish `ha0 : 0 < L.sc.a` using `by linarith`. Establish `hlx` using `logx_nonneg L.sc`. Establish `hLa` using `La_nonneg K hK L.sc`.

Establish `hP0` using `p0_pos D L.sc`. Establish `hc3` using `third_constant_nonneg L C bo hC hbo`. Establish `hb'` using `sc_b'_nonneg L.sc`. Establish `hcG : 0 ≤ cG L` using `by unfold cG; have := L.Sc_pos; linarith`. Establish `hη` using `L.etaSz_pos`.

Establish `hlg : 0 ≤ Real.logb p (2 * L.sc.a)` using `Real.logb_nonneg hp1 (by linarith)`. Establish `hcp0 : 0 ≤ C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)` using `mul_nonneg (mul_nonneg hC (by linarith)) hlg`. Establish `hcp : Real.log p * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) = c1 L C`. Unfold `c1 Real.logb`. Clear the denominators using the available nonvanishing facts.

Establish `hu : 0 ≤ C * Real.log L.sc.x` using `mul_nonneg hC hlx`. Establish `hr : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x` using `mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx`. Establish `hY : 0 < ((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4` using `by positivity`. Establish `hPL` using `prime_rpow_neg_level_le D L.sc p hp`. Establish `hPL0 : 0 ≤ (p : ℝ) ^ (-(L1 D L.sc p : ℝ))` using `Real.rpow_nonneg hp0.le _`.

Establish `hc2 : 0 ≤ c2 L C`. Unfold `c2`. Establish `: 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))` using `mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc4a : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k)` using `mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) hk0.le)`.

Establish `hc4b : 0 ≤ C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k)` using `mul_nonneg hu (div_nonneg ha0.le hP0.le)`. Establish `hc4 : c4 K L C = C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k) + C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k)` using `by unfold c4; ring`. Establish `hlp : 0 ≤ Real.log p / p` using `div_nonneg hl.le hp0.le`. Establish `hLaT : Real.log p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) = Real.log p / p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k))`. Clear the denominators using the available nonvanishing facts.

Establish `hLaT0 : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))` using `mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) (by positivity))`. Distinguish the cases in `h1 : (p : ℝ) < L.sc.p0 D.R.k`. Establish `m1 : p ∈ prB (L.sc.p0 D.R.k)` using `mem_prB.2 ⟨hp, h1⟩`. Distinguish the cases in `h2 : (p : ℝ) < L.sc.X'`. Establish `m2 : p ∈ prB L.sc.X'` using `mem_prB.2 ⟨hp, h2⟩`.

Establish `e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x + C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)))`. Unfold `lo`. Simplify using `only [if_pos hc0, if_pos h1, if_pos (And.intro hc0 h2)]`. Establish `t1 : C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPL ha0.le) hu`. Establish `t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)))` using `mul_nonneg hu (mul_nonneg ha0.le hPL0)`.

Rewrite using `[e, if_pos m1, if_pos m2, if_pos m2]`. Prove the components needed by the constructor for the conclusion. Establish `: C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) = C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) + C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t1'` using `mul_le_mul_of_nonneg_left t1 hl.le`.

Establish `t3` using `mul_nonneg hl.le hc3`. Establish `t4` using `mul_nonneg hlp hc4b`. Rewrite using `[hc4]`. Unfold `c2`. Combine the linear relations using `[hcp, hLaT, t1', t3, t4]`.

Establish `m2 : p ∉ prB L.sc.X'` using `fun h => h2 (mem_prB.1 h).2`. Establish `e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x + 0`. Unfold `lo`. Simplify using `only [if_pos hc0, if_pos h1, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]`. Rewrite using `[e, if_pos m1, if_neg m2, if_neg m2]`.

Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t2 : 0 ≤ Real.log p * (C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)))` using `mul_nonneg hl.le (mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le)))`. Unfold `c2`. Combine the linear relations using `[hcp, t2]`.

Establish `m1 : p ∉ prB (L.sc.p0 D.R.k)` using `fun h => h1 (mem_prB.1 h).2`. Distinguish the cases in `h2 : (p : ℝ) < L.sc.X'`. Establish `m2 : p ∈ prB L.sc.X'` using `mem_prB.2 ⟨hp, h2⟩`. Establish `e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + c3 L C bo + C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2)`. Unfold `lo c3`.

Simplify using `only [if_pos hc0, if_neg h1, if_pos h2, if_pos (And.intro hc0 h2)]`. Establish `hpp : L.sc.a / (p : ℝ) ^ 2 ≤ 1 / p * (L.sc.a / L.sc.p0 D.R.k)`. Rewrite using `[div_mul_div_comm, one_mul]`. Apply `div_le_div_of_nonneg_left ha0.le (by positivity)` to reduce the goal to its premises. Rewrite using `[pow_two]`.

Conclude with `mul_le_mul_of_nonneg_left (not_lt.1 h1) hp0.le`. Establish `t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2)` using `mul_nonneg hu (by positivity)`. Establish `t1 : Real.log p * (C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2)) ≤ Real.log p / p * (C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k))`. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpp hu) hl.le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e, if_neg m1, if_pos m2, if_pos m2]`. Prove the components needed by the constructor for the conclusion. Establish `: C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) = C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) + C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hc4]`.

Combine the linear relations using `[hcp, hLaT, t1]`. Establish `m2 : p ∉ prB L.sc.X'` using `fun h => h2 (mem_prB.1 h).2`. Establish `e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + 0 + 0`. Unfold `lo`. Simplify using `only [if_pos hc0, if_neg h1, if_neg h2, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]`.

Rewrite using `[e, if_neg m1, if_neg m2, if_neg m2]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[hcp]`.
-/
theorem lo_bounds (K : Consts) (hK : 0 ≤ K.La) (L : SizeData₂ D) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo) (p : ℕ) (hp : p.Prime)
    (hc0 : IsResidueClassZero D p) :
    0 ≤ lo K L C bo p ∧
    Real.log p * lo K L C bo p ≤ c1 L C + (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) * c2 L C +
      (if p ∈ prB L.sc.X' then Real.log p else 0) * c3 L C bo +
      (if p ∈ prB L.sc.X' then Real.log p / p else 0) * c4 K L C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hl : 0 < Real.log p := Real.log_pos hp1
  have hk := k_ge D
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have ha0 : 0 < L.sc.a := by linarith
  have hlx := logx_nonneg L.sc
  have hLa := La_nonneg K hK L.sc
  have hP0 := p0_pos D L.sc
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hb' := sc_b'_nonneg L.sc
  have hcG : 0 ≤ cG L := by unfold cG; have := L.Sc_pos; linarith
  have hη := L.etaSz_pos
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hcp0 : 0 ≤ C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) :=
    mul_nonneg (mul_nonneg hC (by linarith)) hlg
  have hcp : Real.log p * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) = c1 L C := by
    unfold c1 Real.logb
    field_simp
  have hu : 0 ≤ C * Real.log L.sc.x := mul_nonneg hC hlx
  have hr : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx
  have hY : 0 < ((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4 := by positivity
  have hPL := prime_rpow_neg_level_le D L.sc p hp
  have hPL0 : 0 ≤ (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) := Real.rpow_nonneg hp0.le _
  have hc2 : 0 ≤ c2 L C := by
    unfold c2
    have : 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
      mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le))
    linarith
  have hc4a : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k) :=
    mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) hk0.le)
  have hc4b : 0 ≤ C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k) := mul_nonneg hu (div_nonneg ha0.le hP0.le)
  have hc4 : c4 K L C = C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k) +
      C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k) := by unfold c4; ring
  have hlp : 0 ≤ Real.log p / p := div_nonneg hl.le hp0.le
  have hLaT : Real.log p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) =
      Real.log p / p * (C * Real.log L.sc.x * (La K L.sc * L.sc.a / D.R.k)) := by
    field_simp
  have hLaT0 : 0 ≤ C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) :=
    mul_nonneg hu (div_nonneg (mul_nonneg hLa ha0.le) (by positivity))
  by_cases h1 : (p : ℝ) < L.sc.p0 D.R.k
  · have m1 : p ∈ prB (L.sc.p0 D.R.k) := mem_prB.2 ⟨hp, h1⟩
    by_cases h2 : (p : ℝ) < L.sc.X'
    · have m2 : p ∈ prB L.sc.X' := mem_prB.2 ⟨hp, h2⟩
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
          C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x +
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) := by
        unfold lo
        simp only [if_pos hc0, if_pos h1, if_pos (And.intro hc0 h2)]
      have t1 : C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) ≤
          C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPL ha0.le) hu
      have t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) :=
        mul_nonneg hu (mul_nonneg ha0.le hPL0)
      rw [e, if_pos m1, if_pos m2, if_pos m2]
      constructor
      · have : C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) =
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
          C * Real.log L.sc.x * (L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))) := by ring
        linarith
      · have t1' := mul_le_mul_of_nonneg_left t1 hl.le
        have t3 := mul_nonneg hl.le hc3
        have t4 := mul_nonneg hlp hc4b
        rw [hc4]
        unfold c2
        linarith [hcp, hLaT, t1', t3, t4]
    · have m2 : p ∉ prB L.sc.X' := fun h => h2 (mem_prB.1 h).2
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
          C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x + 0 := by
        unfold lo
        simp only [if_pos hc0, if_pos h1, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]
      rw [e, if_pos m1, if_neg m2, if_neg m2]
      constructor
      · linarith
      · have t2 : 0 ≤ Real.log p * (C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹))) :=
          mul_nonneg hl.le (mul_nonneg hu (mul_nonneg ha0.le (inv_nonneg.2 hY.le)))
        unfold c2
        linarith [hcp, t2]
  · have m1 : p ∉ prB (L.sc.p0 D.R.k) := fun h => h1 (mem_prB.1 h).2
    by_cases h2 : (p : ℝ) < L.sc.X'
    · have m2 : p ∈ prB L.sc.X' := mem_prB.2 ⟨hp, h2⟩
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + c3 L C bo +
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) := by
        unfold lo c3
        simp only [if_pos hc0, if_neg h1, if_pos h2, if_pos (And.intro hc0 h2)]
      have hpp : L.sc.a / (p : ℝ) ^ 2 ≤ 1 / p * (L.sc.a / L.sc.p0 D.R.k) := by
        rw [div_mul_div_comm, one_mul]
        apply div_le_div_of_nonneg_left ha0.le (by positivity)
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (not_lt.1 h1) hp0.le
      have t0 : 0 ≤ C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2) := mul_nonneg hu (by positivity)
      have t1 : Real.log p * (C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2)) ≤
          Real.log p / p * (C * Real.log L.sc.x * (L.sc.a / L.sc.p0 D.R.k)) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpp hu) hl.le
        calc _ ≤ Real.log p * (C * Real.log L.sc.x * (1 / p * (L.sc.a / L.sc.p0 D.R.k))) := this
          _ = _ := by ring
      rw [e, if_neg m1, if_pos m2, if_pos m2]
      constructor
      · have : C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a / (p : ℝ) ^ 2) =
          C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
          C * Real.log L.sc.x * (L.sc.a / (p : ℝ) ^ 2) := by ring
        linarith
      · rw [hc4]
        linarith [hcp, hLaT, t1]
    · have m2 : p ∉ prB L.sc.X' := fun h => h2 (mem_prB.1 h).2
      have e : lo K L C bo p = C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) + 0 + 0 := by
        unfold lo
        simp only [if_pos hc0, if_neg h1, if_neg h2, if_neg (fun h : IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' => h2 h.2)]
      rw [e, if_neg m1, if_neg m2, if_neg m2]
      constructor
      · linarith
      · linarith [hcp]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hl : 0 < Real.log p` using `Real.log_pos hp1`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hl2p : Real.log 2 ≤ Real.log p` using `Real.log_le_log (by norm_num) hp2`.

Establish `ha` using `sc_one_lt_a s`. Establish `hla : 0 ≤ Real.log s.a` using `Real.log_nonneg ha.le`. Establish `hlb : 0 ≤ Real.logb p s.a` using `Real.logb_nonneg hp1 ha.le`. Establish `hCf : 0 ≤ C * (D.R.f : ℝ)` using `mul_nonneg hC (Nat.cast_nonneg _)`. Prove the components needed by the constructor for the conclusion.

Unfold `fl`. Establish `h1 : 0 ≤ C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a` using `mul_nonneg (mul_nonneg hCf (by positivity)) hlb`. Establish `h2 : 0 ≤ C * (D.R.f : ℝ) * Real.logb p s.a ^ 2` using `mul_nonneg hCf (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : Real.log p * fl D s C p = C * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log s.a + Real.log s.a ^ 2 / Real.log p)`.

Unfold `fl Real.logb`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Unfold `cfl`. Apply `mul_le_mul_of_nonneg_left _ hCf` to reduce the goal to its premises.

Establish `: Real.log s.a ^ 2 / Real.log p ≤ Real.log s.a ^ 2 / Real.log 2` using `div_le_div_of_nonneg_left (by positivity) hl2 hl2p`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fl_bounds (D : D7) (s : Scale) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : p.Prime) :
    0 ≤ fl D s C p ∧ Real.log p * fl D s C p ≤ cfl D s C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 < Real.log p := Real.log_pos hp1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have ha := sc_one_lt_a s
  have hla : 0 ≤ Real.log s.a := Real.log_nonneg ha.le
  have hlb : 0 ≤ Real.logb p s.a := Real.logb_nonneg hp1 ha.le
  have hCf : 0 ≤ C * (D.R.f : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
  constructor
  · unfold fl
    have h1 : 0 ≤ C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a := mul_nonneg (mul_nonneg hCf (by positivity)) hlb
    have h2 : 0 ≤ C * (D.R.f : ℝ) * Real.logb p s.a ^ 2 := mul_nonneg hCf (by positivity)
    linarith
  · have e : Real.log p * fl D s C p = C * (D.R.f : ℝ) * (Nm D ^ 2 * Real.log s.a + Real.log s.a ^ 2 / Real.log p) := by
      unfold fl Real.logb
      field_simp
    rw [e]
    unfold cfl
    apply mul_le_mul_of_nonneg_left _ hCf
    have : Real.log s.a ^ 2 / Real.log p ≤ Real.log s.a ^ 2 / Real.log 2 :=
      div_le_div_of_nonneg_left (by positivity) hl2 hl2p
    linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
