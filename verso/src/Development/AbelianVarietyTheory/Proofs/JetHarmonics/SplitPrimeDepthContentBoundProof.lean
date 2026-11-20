import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement

open Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth
open scoped BigOperators

namespace GlobalTheory.SplitPackageBound

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `p hp q hq hpq`. Conclude with `(h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩`. Introduce `z _`.

Take `⟨p, hp, -⟩` from `h z`. Conclude with `⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩`.
-/
theorem sum_reps {M : Type} [AddCommMonoid M] (P : RF.Par) (Z : Finset P.Pl)
    (h : RF.IsReps P Z) (W : P.Pl → M) :
    ∑ z ∈ Z, ∑ a, RF.alongOrb P z W a = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩
      ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

/- English proof (translation)
Use `sum_reps P Z h (fun _ => (1 : ℕ))` as an intermediate fact. Simplify `this` using `[RF.alongOrb]`.
-/
theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) :
    Z.card * Fintype.card (ZMod P.d) = Fintype.card P.Pl := by
  have := sum_reps P Z h (fun _ => (1 : ℕ))
  simpa [RF.alongOrb] using this

/- English proof (translation)
Establish `hsub : ∀ r, Finset.Icc 1 (min K r) ⊆ Finset.Icc 1 K` using `fun r => Finset.Icc_subset_Icc_right (min_le_left _ _)`. Unfold `RF.restDeg monDeg`. Rewrite using `[Fin.sum_univ_two]`. Use `Nat.add_le_add (Finset.sum_le_sum (N := ℕ) fun a _ => ?_) (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)` and prove the remaining obligations. Use `le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hk : k = n <;> simp [hk]`. Use `le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem deg_le {d : ℕ} [NeZero d] (rk : Fin 2 → ZMod d → ℕ) (n K : ℕ)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    (∑ a, monDeg K (rk 0 a) (fun k => if k = n then 0 else ga 0 a k)) +
      (∑ a, monDeg K (rk 1 a) (ga 1 a)) ≤ RF.restDeg (fun _ => 0) n ga K := by
  have hsub : ∀ r, Finset.Icc 1 (min K r) ⊆ Finset.Icc 1 K := fun r =>
    Finset.Icc_subset_Icc_right (min_le_left _ _)
  unfold RF.restDeg monDeg
  rw [Fin.sum_univ_two]
  refine Nat.add_le_add (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
    (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = n <;> simp [hk]
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    simp

/- English proof (translation)
Take `⟨R, Z, hZ, hbig, ga, W, nW, T, θ, rest, ν, hW, hr, hD, hV⟩` from `Pk`. Simplify using `only`. Establish `hVl` using `R.hVl`. Establish `hl' : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk` using `hP.mk_le`. Establish `hrr` using `hP.r_eq`. Set `e0 : P.Pl → ZMod P.d → ℕ → ℕ` to `fun z a k => if k = P.k - 1 then 0 else ga z 0 a k`. Use `hV (fun z => (RF.GlobalTheory.mon 0 (e0 z) P.r, (RF.monDegAll (R.X z) 0 (e0 z) P.r : ℝ) / ((R.V.l : ℝ) - 1)) :: (RF.GlobalTheory.mon 1 (ga z 1) P.r, (RF.monDegAll (R.X z) 1 (ga z 1) P.r : ℝ) / ((R.V.l : ℝ) - 1)) :: (Finset.univ : Finset (ZMod P.d)).toList.map fun a => (RF.GlobalT …` as an intermediate fact.

Use `this.trans ?_` and prove the remaining obligations. Simplify using `only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList, Function.comp_def, hVl]`. Rewrite using `[hW.rest_eq, ← sum_reps P Z hZ (fun z => (W z : ℝ)), Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun z hz => ?_` and prove the remaining obligations. Rewrite using `[(R.hn z).2, ← add_assoc, add_comm, ← Finset.sum_mul, mul_div_assoc, ← add_div]`.

Use `add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hl'.le)` and prove the remaining obligations. Establish `h` using `deg_le (R.X z).rkF (P.k - 1) P.r (ga z)`. Simplify using `only [Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]`. Conclude with `h` after adjusting the coercions. Introduce `z hz p hp`.

Simplify using `only [List.mem_cons, List.mem_map] at hp`. Break down `hp with rfl | rfl | ⟨a, -, rfl⟩` into its components or cases. Conclude with `(hM R.C R.V _ _ _ (R.X z) (R.F z) 0 _ _).1`. Conclude with `(hM R.C R.V _ _ _ (R.X z) (R.F z) 1 _ _).1`. Conclude with `(hC R.C R.V _ _ _ (R.X z) (R.F z) 0 a (hbig z hz a) _).2 (hbig z hz)`.

Simplify using `only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ]`. Establish `hc` using `card_reps P Z hZ`. Rewrite `hc` using `[hP.card]`. Establish `hpos : 1 ≤ Fintype.card (ZMod P.d)` using `Fintype.card_pos`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun z hz => ?_` and prove the remaining obligations. Establish `: (R.X z).n ≤ P.r` using `by rw [(R.hn z).1]; omega`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = 3 * P.r * P.f := by`. Rewrite using `[Finset.sum_const, smul_eq_mul, ← hc]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ nW := by nlinarith`. Introduce `z hz g a k`. Simplify using `only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.wt]`. Take `⟨hn, hm⟩` from `R.hn z`.

Establish `hb` using `hbig z hz`. Establish `hm' : (R.X z).j + (R.X z).j' = P.m` using `hm`. Establish `h0 : (R.X z).rkF 0 a = (R.X z).n + (R.X z).j` using `(R.X z).rk_big 0 a (hb a)`. Establish `h1 : (R.X z).rkF 1 a = (R.X z).j'` using `(R.X z).rk_small 1 a fun h => ((R.X z).big_compl 0 a).1 (by simpa using h) (hb a)`. Establish `hs` using `hW.supp z hz g a k`.

Establish `hmain` using `hW.main z hz a`. Use `fin_cases g`. Simplify using `only [Fin.zero_eta, true_and, zero_ne_one, false_and, if_false, zero_add] at hs hmain ⊢`. Distinguish the cases in `hkn : k = P.k - 1`. Substitute `hkn` using the available equality.

Rewrite using `[hmain]`. Simplify using `[e0, hn]`. Establish `: k ≠ (R.X z).n` using `by omega`. Distinguish the cases in `hz0 : ga z 0 a k = 0`. Simplify using `[e0, hkn, this, hz0]`.

Establish `h2` using `hs hz0`. Rewrite using `[if_pos (by omega)]`. Simplify using `[e0, hkn, this]`. Simplify using `only [Fin.mk_one, true_and, one_ne_zero, false_and, if_false, zero_add, Finset.sum_const_zero, add_zero] at hs ⊢`. Distinguish the cases in `hz0 : ga z 1 a k = 0`.

Simplify using `[hz0]`. Establish `h2` using `hs hz0`. Rewrite using `[if_pos (by omega)]`.
-/
theorem nu_le (hC : RF.CHSupply) (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (C1 : ℝ) (hP : ParOK P)
    (hl : l.Prime) (Pk : RF.PkgSplit P l C1) :
    Pk.ν ≤ (∑ z, (Pk.W z : ℝ)) * P.m / ((l : ℝ) - 1) + Pk.rest / ((l : ℝ) - 1) := by
  obtain ⟨R, Z, hZ, hbig, ga, W, nW, T, θ, rest, ν, hW, hr, hD, hV⟩ := Pk
  dsimp only
  have hVl := R.hVl
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    linarith
  have hk := hP.mk_le
  have hrr := hP.r_eq
  let e0 : P.Pl → ZMod P.d → ℕ → ℕ := fun z a k =>
    if k = P.k - 1 then 0 else ga z 0 a k
  have := hV (fun z =>
    (RF.GlobalTheory.mon 0 (e0 z) P.r, (RF.monDegAll (R.X z) 0 (e0 z) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (RF.GlobalTheory.mon 1 (ga z 1) P.r, (RF.monDegAll (R.X z) 1 (ga z 1) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (Finset.univ : Finset (ZMod P.d)).toList.map fun a =>
      (RF.GlobalTheory.ch 0 a (RF.alongOrb P z W a),
        ((RF.alongOrb P z W a : ℕ) : ℝ) * ((R.X z).m / ((R.V.l : ℝ) - 1)))) ?_ ?_ ?_
  · refine this.trans ?_
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, hVl]
    rw [hW.rest_eq, ← sum_reps P Z hZ (fun z => (W z : ℝ)), Finset.sum_mul, Finset.sum_div,
      Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [(R.hn z).2, ← add_assoc, add_comm, ← Finset.sum_mul, mul_div_assoc, ← add_div]
    refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hl'.le)
    have h := deg_le (R.X z).rkF (P.k - 1) P.r (ga z)
    simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    exact_mod_cast h
  · intro z hz p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨a, -, rfl⟩
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 0 _ _).1
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 1 _ _).1
    · exact (hC R.C R.V _ _ _ (R.X z) (R.F z) 0 a (hbig z hz a) _).2 (hbig z hz)
  · simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have hc := card_reps P Z hZ
    rw [hP.card] at hc
    have hpos : 1 ≤ Fintype.card (ZMod P.d) := Fintype.card_pos
    calc _ ≤ ∑ z ∈ Z, 3 * P.r * Fintype.card (ZMod P.d) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have : (R.X z).n ≤ P.r := by rw [(R.hn z).1]; omega
          nlinarith
      _ = 3 * P.r * P.f := by
          rw [Finset.sum_const, smul_eq_mul, ← hc]; ring
      _ ≤ nW := by nlinarith
  · intro z hz g a k
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.wt]
    obtain ⟨hn, hm⟩ := R.hn z
    have hb := hbig z hz
    have hm' : (R.X z).j + (R.X z).j' = P.m := hm
    have h0 : (R.X z).rkF 0 a = (R.X z).n + (R.X z).j := (R.X z).rk_big 0 a (hb a)
    have h1 : (R.X z).rkF 1 a = (R.X z).j' :=
      (R.X z).rk_small 1 a fun h => ((R.X z).big_compl 0 a).1 (by simpa using h) (hb a)
    have hs := hW.supp z hz g a k
    have hmain := hW.main z hz a
    fin_cases g
    · simp only [Fin.zero_eta, true_and, zero_ne_one, false_and, if_false, zero_add] at hs hmain ⊢
      by_cases hkn : k = P.k - 1
      · subst hkn
        rw [hmain]
        simp [e0, hn]
      · have : k ≠ (R.X z).n := by omega
        by_cases hz0 : ga z 0 a k = 0
        · simp [e0, hkn, this, hz0]
        · have h2 := hs hz0
          rw [if_pos (by omega)]
          simp [e0, hkn, this]
    · simp only [Fin.mk_one, true_and, one_ne_zero, false_and, if_false, zero_add,
        Finset.sum_const_zero, add_zero] at hs ⊢
      by_cases hz0 : ga z 1 a k = 0
      · simp [hz0]
      · have h2 := hs hz0
        rw [if_pos (by omega)]

/- English proof (translation)
Introduce `C1 hC1`. Use `⟨2 * (1 + 2 * C1), by positivity, fun P l hP hl Pk => ?_⟩` and prove the remaining obligations. Establish `hν` using `nu_le hC hM P l C1 hP hl Pk`. Establish `hD` using `Pk.deg`. Establish `h2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`.

Establish `hl' : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `hT : 0 ≤ Pk.T` using `le_trans zero_le_one hD.T_one`. Establish `hSE` using `hP.SE_nonneg`. Establish `h1 : Pk.T * ∑ z, (Pk.W z : ℝ) ≤ ∑ z, P.w z + P.f * (C1 * P.SE)`. Rewrite using `[Finset.mul_sum]`.

Use `(Finset.sum_le_sum fun z _ => hD.TW_hi z).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hP.card, nsmul_eq_mul]`. Establish `hw : 0 ≤ ∑ z, P.w z` using `Finset.sum_nonneg fun z _ => (hD.w_pos z).le`. Establish `hm : (0 : ℝ) ≤ P.m` using `Nat.cast_nonneg _`. Establish `hmk : (P.m : ℝ) ≤ P.k` using `by exact_mod_cast (by have := hP.mk_le; omega : P.m ≤ P.k)`.

Establish `hf : (0 : ℝ) ≤ P.f` using `Nat.cast_nonneg _`. Use `set A : ℝ := P.m * ∑ z, P.w z with hA`. Use `set B : ℝ := P.f * P.k * P.SE with hB`. Establish `hA0 : 0 ≤ A` using `mul_nonneg hm hw`. Establish `hB0 : 0 ≤ B` using `mul_nonneg (mul_nonneg hf (Nat.cast_nonneg _)) hSE`.

Establish `h3 : Pk.T * ((∑ z, (Pk.W z : ℝ)) * P.m + Pk.rest) ≤ (1 + 2 * C1) * (A + B)`. Establish `e1` using `mul_le_mul_of_nonneg_right h1 hm`. Establish `e2 : P.f * (C1 * P.SE) * P.m ≤ C1 * B`. Use `mul_le_mul_of_nonneg_left hmk (mul_nonneg hf (mul_nonneg hC1 hSE))` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `e3` using `hD.rest_le`. Establish `e4` using `mul_nonneg hC1 hA0`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : 0 ≤ (1 + 2 * C1) * (A + B)` using `by positivity`. Use `(mul_le_mul_of_nonneg_left hν hT).trans ?_` and prove the remaining obligations.

Rewrite using `[← add_div, ← mul_div_assoc, ← mul_div_assoc]`. Use `(div_le_div_of_nonneg_right h3 hl'.le).trans ?_` and prove the remaining obligations. Rewrite using `[div_le_div_iff₀ hl' (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem splitBd_of_supplies (hC : RF.CHSupply) (hM : RF.MONSupply) : SplitBd := by
  intro C1 hC1
  refine ⟨2 * (1 + 2 * C1), by positivity, fun P l hP hl Pk => ?_⟩
  have hν := nu_le hC hM P l C1 hP hl Pk
  have hD := Pk.deg
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hT : 0 ≤ Pk.T := le_trans zero_le_one hD.T_one
  have hSE := hP.SE_nonneg
  have h1 : Pk.T * ∑ z, (Pk.W z : ℝ) ≤ ∑ z, P.w z + P.f * (C1 * P.SE) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun z _ => hD.TW_hi z).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hP.card, nsmul_eq_mul]
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hD.w_pos z).le
  have hm : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hmk : (P.m : ℝ) ≤ P.k := by exact_mod_cast (by have := hP.mk_le; omega : P.m ≤ P.k)
  have hf : (0 : ℝ) ≤ P.f := Nat.cast_nonneg _
  set A : ℝ := P.m * ∑ z, P.w z with hA
  set B : ℝ := P.f * P.k * P.SE with hB
  have hA0 : 0 ≤ A := mul_nonneg hm hw
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hf (Nat.cast_nonneg _)) hSE
  have h3 : Pk.T * ((∑ z, (Pk.W z : ℝ)) * P.m + Pk.rest) ≤ (1 + 2 * C1) * (A + B) := by
    have e1 := mul_le_mul_of_nonneg_right h1 hm
    have e2 : P.f * (C1 * P.SE) * P.m ≤ C1 * B := by
      have := mul_le_mul_of_nonneg_left hmk (mul_nonneg hf (mul_nonneg hC1 hSE))
      calc _ ≤ _ := this
        _ = _ := by rw [hB]; ring
    have e3 := hD.rest_le
    have e4 := mul_nonneg hC1 hA0
    nlinarith
  have h4 : 0 ≤ (1 + 2 * C1) * (A + B) := by positivity
  refine (mul_le_mul_of_nonneg_left hν hT).trans ?_
  rw [← add_div, ← mul_div_assoc, ← mul_div_assoc]
  refine (div_le_div_of_nonneg_right h3 hl'.le).trans ?_
  rw [div_le_div_iff₀ hl' (by linarith)]
  nlinarith

end GlobalTheory.SplitPackageBound

/- English proof (translation)
The claim follows from `GlobalTheory.SplitPackageBound.splitBd_of_supplies GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2`.
-/
theorem GlobalTheory.GoodDepth.splitBd : SplitBd :=
  GlobalTheory.SplitPackageBound.splitBd_of_supplies GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2
