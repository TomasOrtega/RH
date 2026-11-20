import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.TopPair

open GlobalTheory.SignedHC Finset

variable (D : D7) (τ : D.what₂.Tau)

local notation "Γ" => grid D τ

/- English proof (translation)
Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩`.
-/
theorem grid_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩

/- English proof (translation)
Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩`.
-/
theorem grid_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩

/- English proof (translation)
Take `⟨i, rfl⟩ : ∃ i', i = i' + 2` from `⟨i - 2, by omega⟩`. Conclude with `GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩`.
-/
theorem grid_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  exact GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩

/- English proof (translation)
Rewrite using `[grid_e D τ h1 h2, grid_b D τ h1 h2]`. Conclude with `(D.hc τ).gap_be _`.
-/
theorem grid_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
  rw [grid_e D τ h1 h2, grid_b D τ h1 h2]
  exact (D.hc τ).gap_be _

/- English proof (translation)
Rewrite using `[grid_e D τ h1 (by omega), grid_b D τ (by omega) h2]`. Take `⟨l, rfl⟩ : ∃ l', l = l' + 1` from `⟨l - 1, by omega⟩`. Conclude with `(D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))`.
-/
theorem grid_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
  rw [grid_e D τ h1 (by omega), grid_b D τ (by omega) h2]
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))

/- English proof (translation)
Proceed by induction on `l', h using Nat.le_induction with`. Consider the case `base`. Combine the linear relations using `[grid_be D τ (l := l + 1) (by omega) h2, grid_eb D τ h1 h2]`. Consider the case `succ n hn ih`. Use `ih (by omega)` as an intermediate fact.

Establish `e1` using `grid_be D τ (l := n + 1) (by omega) h2`. Establish `e2` using `grid_eb D τ (l := n) (by omega) h2`. Establish `: (0 : ℚ) ≤ D.R.t` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
  induction l', h using Nat.le_induction with
  | base =>
    linarith [grid_be D τ (l := l + 1) (by omega) h2, grid_eb D τ h1 h2]
  | succ n hn ih =>
    have := ih (by omega)
    have e1 := grid_be D τ (l := n + 1) (by omega) h2
    have e2 := grid_eb D τ (l := n) (by omega) h2
    have : (0 : ℚ) ≤ D.R.t := by positivity
    linarith

/- English proof (translation)
Establish `hm : 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k`. Rewrite using `[grid_v D τ hk le_rfl, grid_b D τ le_rfl hm]`. Establish `e1` using `(D.hc τ).u_last_gt (by omega) (by omega)`.

Establish `e2` using `(D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `Fin.ext (by simp only; omega)`. Simplify using `only [e3] at e2`. Conclude with `e1.trans e2`. Establish `base' : -((Γ).b 1) < (Γ).v D.R.k` using `by exact_mod_cast base`.

Establish `step : (Γ).v D.R.k ≤ (Γ).v i`. Break down `h2.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `((Γ).v_anti i D.R.k h1 h le_rfl).le`. Establish `: -((Γ).b 1) + 1 ≤ (Γ).v i` using `by omega`.

Conclude with `this` after adjusting the coercions.
-/
theorem grid_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
    rw [grid_v D τ hk le_rfl, grid_b D τ le_rfl hm]
    have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    simp only [e3] at e2
    exact e1.trans e2
  have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
  have step : (Γ).v D.R.k ≤ (Γ).v i := by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
  have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
  exact_mod_cast this

/- English proof (translation)
Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Establish `: (0 : ℚ) ≤ (Γ).ga` using `by positivity`. Combine the linear relations using `[GlobalTheory.ChiGrid.a_add_le (G := Γ) h]`.
-/
theorem grid_a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ (Γ).ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]

/- English proof (translation)
Use `abs_le.1 (abs_sub_le_of_mem_block h)` as an intermediate fact. Establish `e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1` using `by push_cast; rfl`. Rewrite `this` using `[e]`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`.
-/
theorem grid_blockMPlus_bd {l : ℕ} {x : ℚ} (h : x ∈ (Γ).blockMPlus l) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((Γ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block h)
  have e : (((Γ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
  rw [e] at this
  constructor <;> linarith [this.1, this.2]

/- English proof (translation)
Use `(isLeast_gap D).1.2.1` as an intermediate fact. Use `show sLen D < gap D`. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_s_lt_gap : (Γ).s < (Γ).ga := by
  have := (isLeast_gap D).1.2.1
  show sLen D < gap D
  omega

/- English proof (translation)
The claim follows from `GlobalTheory.ChiGrid.odd_sLen D`.
-/
theorem grid_length_odd : Odd (Γ).s := GlobalTheory.ChiGrid.odd_sLen D

/- English proof (translation)
Establish `hm : 1 ≤ D.R.m` using `by omega`. Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `hg : (0 : ℚ) ≤ (Γ).ga` using `by positivity`. Take `⟨y1, y2⟩` from `grid_blockMPlus_bd D τ hy`.

Establish `hbe` using `grid_be D τ (l := 1) le_rfl hm`. Establish `he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1)`. Break down `Nat.eq_zero_or_pos j with rfl | h` into its components or cases. Conclude with `le_rfl`. Combine the linear relations using `[grid_e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]`.

Establish `hlow : y < -((Γ).b 1 : ℚ)` using `by linarith`. Establish `hc2` using `grid_cloud D τ (i := 2) le_rfl hk`. Establish `ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2` using `(Γ).a_m`. Break down `GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩` into its components or cases. Take `⟨i, hi, rfl⟩` from `GridData.mem_tops.1 h`.

Combine the linear relations using `[grid_a_le D τ hi]`. Take `⟨i, h1, h2, rfl⟩` from `GridData.mem_cloudHalf.1 h`. Use `grid_cloud D τ h1 h2` as an intermediate fact. Simplify using `only [GridData.vHalf]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (grid_length_odd D τ).pos (grid_s_lt_gap D τ) h1 h2 h).1` as an intermediate fact. Combine the linear relations using `[grid_a_le D τ h2]`. Use `grid_e_lt D τ h1 (by omega : l < j + 1) hj` as an intermediate fact. Use `(grid_blockMPlus_bd D τ h).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_weightX_above {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (Γ).weightX j)
    (hy : y ∈ (Γ).blockMPlus (j + 1)) : y < x := by
  have hm : 1 ≤ D.R.m := by omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have hg : (0 : ℚ) ≤ (Γ).ga := by positivity
  obtain ⟨y1, y2⟩ := grid_blockMPlus_bd D τ hy
  have hbe := grid_be D τ (l := 1) le_rfl hm
  have he1 : ((Γ).e 1 : ℚ) ≤ (Γ).e (j + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact le_rfl
    · linarith [grid_e_lt D τ (l := 1) (l' := j + 1) le_rfl (by omega) hj]
  have hlow : y < -((Γ).b 1 : ℚ) := by linarith
  have hc2 := grid_cloud D τ (i := 2) le_rfl hk
  have ham : (Γ).a (Γ).m = (Γ).v 2 + (Γ).ga + 1 / 2 := (Γ).a_m
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    linarith [grid_a_le D τ hi]
  · obtain ⟨i, h1, h2, rfl⟩ := GridData.mem_cloudHalf.1 h
    have := grid_cloud D τ h1 h2
    simp only [GridData.vHalf]
    linarith
  · have := (GlobalTheory.ChiGrid.blockC'_between (grid_nearMid D τ) (grid_length_odd D τ).pos (grid_s_lt_gap D τ) h1 h2 h).1
    linarith [grid_a_le D τ h2]
  · have := grid_e_lt D τ h1 (by omega : l < j + 1) hj
    have := (grid_blockMPlus_bd D τ h).1
    linarith

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (grid_length_odd D τ)`. Consider the case `succ j ih`. Rewrite using `[(Γ).weightX_succ]`. Introduce `x hx`.

Break down `mem_union.1 hx with h | h` into its components or cases. Conclude with `ih x h`. Take `⟨a, -, rfl⟩` from `mem_block.1 h`. Take `⟨u, hu⟩` from `D.R.t_odd`. Establish `e : ((Γ).t : ℚ) = 2 * u + 1`.

Establish `: ((Γ).t : ℚ) = D.R.t` using `rfl`. Rewrite using `[this, hu]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(Γ).e (j + 1) + u - a, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem grid_inCoset_weightX {j : ℕ} : InCoset (1 / 2) ((Γ).weightX j) := by
  induction j with
  | zero => exact GlobalTheory.ChiGrid.inCoset_weightX_zero (grid_length_odd D τ)
  | succ j ih =>
    rw [(Γ).weightX_succ]
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact ih x h
    · obtain ⟨a, -, rfl⟩ := mem_block.1 h
      obtain ⟨u, hu⟩ := D.R.t_odd
      have e : ((Γ).t : ℚ) = 2 * u + 1 := by
        have : ((Γ).t : ℚ) = D.R.t := rfl
        rw [this, hu]; push_cast; ring
      refine ⟨-(Γ).e (j + 1) + u - a, ?_⟩
      push_cast
      rw [e]
      ring

/- English proof (translation)
Establish `c1 : (Γ).tops.card ≤ D.R.m + 1`. Unfold `GridData.tops`. Conclude with `card_image_le.trans (by simp; rfl)`. Establish `c2 : (Γ).cloudHalf.card ≤ D.R.k - 1`. Unfold `GridData.cloudHalf`.

Use `card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Nat.card_Icc]`. Use `show D.R.k + 1 - 2 ≤ D.R.k - 1`. Use linear arithmetic over natural numbers and integers. Establish `c3 : ((Icc 1 (Γ).m).biUnion (Γ).blockC').card ≤ D.R.m * (sLen D - 1)`.

Use `card_biUnion_le.trans ?_` and prove the remaining obligations. Simplify using `only [GridData.blockC', card_block, sum_const, Nat.card_Icc, smul_eq_mul]`. Use `show (D.R.m + 1 - 1) * (sLen D - 1) ≤ _`. Simplify using the standard rewrite rules. Establish `c4 : ((Icc 1 j).biUnion (Γ).blockMPlus).card ≤ j * (D.R.t + 1)`.

Use `card_biUnion_le.trans ?_` and prove the remaining obligations. Simplify using `only [GridData.blockMPlus, card_block, sum_const, Nat.card_Icc, smul_eq_mul]`. Use `show (j + 1 - 1) * (D.R.t + 1) ≤ _`. Simplify using the standard rewrite rules. Establish `hs : 1 ≤ sLen D` using `(grid_length_odd D τ).pos`.

Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `e : D.R.m * sLen D = D.R.m * (sLen D - 1) + D.R.m`. Rewrite using `[Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hs)]`. Rewrite using `[GridData.weightX, GridData.entries_lam]`. Use `(card_union_le _ _).trans ?_` and prove the remaining obligations.

Use `(Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_card_weightX_le (j : ℕ) : ((Γ).weightX j).card ≤ D.R.k + D.R.m * sLen D + j * (D.R.t + 1) := by
  have c1 : (Γ).tops.card ≤ D.R.m + 1 := by
    unfold GridData.tops
    exact card_image_le.trans (by simp; rfl)
  have c2 : (Γ).cloudHalf.card ≤ D.R.k - 1 := by
    unfold GridData.cloudHalf
    refine card_image_le.trans ?_
    rw [Nat.card_Icc]
    show D.R.k + 1 - 2 ≤ D.R.k - 1
    omega
  have c3 : ((Icc 1 (Γ).m).biUnion (Γ).blockC').card ≤ D.R.m * (sLen D - 1) := by
    refine card_biUnion_le.trans ?_
    simp only [GridData.blockC', card_block, sum_const, Nat.card_Icc, smul_eq_mul]
    show (D.R.m + 1 - 1) * (sLen D - 1) ≤ _
    simp
  have c4 : ((Icc 1 j).biUnion (Γ).blockMPlus).card ≤ j * (D.R.t + 1) := by
    refine card_biUnion_le.trans ?_
    simp only [GridData.blockMPlus, card_block, sum_const, Nat.card_Icc, smul_eq_mul]
    show (j + 1 - 1) * (D.R.t + 1) ≤ _
    simp
  have hs : 1 ≤ sLen D := (grid_length_odd D τ).pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have e : D.R.m * sLen D = D.R.m * (sLen D - 1) + D.R.m := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hs)]
  rw [GridData.weightX, GridData.entries_lam]
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_
  omega

/- English proof (translation)
Introduce `D hS j τ hj`. Use `set G := grid D τ with hG`. Establish `hj' : j + 1 ≤ D.R.m` using `hj`. Establish `hce : (D.hc τ).e ⟨j, hj⟩ = ((G.e (j + 1) : ℤ) : ℚ)`. Use `grid_e D τ (l := j + 1) (by omega) hj'` as an intermediate fact.

Simplify using `only [Nat.add_sub_cancel] at this`. Conclude with `this.symm`. Use `set c : ℚ := -(D.hc τ).e ⟨j, hj⟩ with hc`. Establish `hblock : G.blockMPlus (j + 1) = TPar.block c (D.R.t + 1)`. Rewrite using `[hc, hce]`.

Both sides reduce to the same expression. Establish `habove : ∀ x ∈ G.weightX j, c + (D.R.t : ℚ) / 2 + 1 ≤ x`. Introduce `x hx`. Establish `htop : c + (D.R.t : ℚ) / 2 ∈ TPar.block c (D.R.t + 1)` using `mem_block.2 ⟨0, by omega, by push_cast; ring⟩`. Establish `hlt` using `grid_weightX_above D τ hj' hx (hblock ▸ htop)`.

Take `⟨z, hz⟩` from `grid_inCoset_weightX D τ (j := j) x hx`. Take `⟨u, hu⟩` from `D.R.t_odd`. Establish `ht : (D.R.t : ℚ) = 2 * u + 1` using `by rw [hu]; push_cast; ring`. Take `⟨w, hw⟩ : ∃ w : ℤ, c = w` from `⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩`. Rewrite `hlt`, the goal using `[hz, hw, ht]`.

Establish `: (w : ℚ) + u < z` using `by linarith`. Establish `h2 : w + u < z` using `by exact_mod_cast this`. Establish `h3 : ((w + u + 1 : ℤ) : ℚ) ≤ z` using `by exact_mod_cast Int.add_one_le_iff.2 h2`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hX : parXp D j τ = G.parX j` using `rfl`. Establish `hX' : parXp D (j + 1) τ = G.parX (j + 1)` using `rfl`. Establish `hpart : partner (D.R.t + 1) true c c (G.parX j) = G.parX (j + 1)`. Unfold `partner`. Establish `h1 : ((G.parX j).image fun x : ℚ × Bool => (x.1 - c + c, if x.1 < c then !x.2 else x.2)) = G.parX j`.

Rewrite using `[← image_id (s := G.parX j)]`. Rewrite using `[image_image]`. Use `image_congr fun x hx => ?_` and prove the remaining obligations. Establish `hx1 : x.1 ∈ G.weightX j` using `(mem_plus.1 hx).1`. Use `habove _ hx1` as an intermediate fact.

Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`. Establish `hn : ¬ x.1 < c` using `by linarith`. Simplify using `[hn]`. Rewrite using `[h1, GridData.parX, GridData.parX, GridData.weightX_succ, plus_union, hblock]`. Both sides reduce to the same expression.

Establish `hT : (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2 = (D.R.t : ℚ) / 2 + 1` using `by push_cast; ring`. Establish `hne : (G.parX j).Nonempty`. Use `⟨(G.a 0, true), mem_plus.2 ⟨GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)), rfl⟩⟩` and prove the remaining obligations. Establish `hcos : InCoset (c + (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (entries (G.parX j))`. Rewrite using `[GridData.parX, entries_plus, hT]`.

Introduce `x hx`. Take `⟨z, hz⟩` from `grid_inCoset_weightX D τ (j := j) x hx`. Take `⟨u, hu⟩` from `D.R.t_odd`. Establish `ht : (D.R.t : ℚ) = 2 * u + 1` using `by rw [hu]; push_cast; ring`. Take `⟨w, hw⟩ : ∃ w : ℤ, c = w` from `⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩`.

Use `⟨z - w - u - 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hw, ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfar : FarFrom c ((((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (G.parX j)`.

Rewrite using `[hT]`. Introduce `x hx`. Rewrite `hx` using `[GridData.parX, entries_plus]`. Use `habove x hx` as an intermediate fact. Establish `h0 : (0 : ℚ) ≤ D.R.t` using `by positivity`.

Rewrite using `[abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : (G.parX j).card + (D.R.t + 1) ≤ bigN D`. Rewrite using `[GridData.parX, ← (isRegular_plus _).card_entries, entries_plus]`. Use `grid_card_weightX_le D τ j` as an intermediate fact.

Establish `e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1)` using `rfl`. Establish `: (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1)` using `Nat.mul_le_mul_right _ hj'`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN : 1800 < bigN D`.

Establish `h1` using `hS.1`. Establish `e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1)` using `rfl`. Establish `: D.R.m ≤ D.R.m * (D.R.t + sLen D + 1)` using `Nat.le_mul_of_pos_right _ (by omega)`. Unfold `Ranks.r at h1`. Use linear arithmetic over natural numbers and integers.

Establish `hgap : ∀ E : Finset ℚ, GapOver (plus E) (2 * (bigN D : ℚ) ^ 3)`. Introduce `E x hx y hy hxy`. Conclude with `absurd ((mem_plus.1 hx).2.trans (mem_plus.1 hy).2.symm) hxy`. Establish `key` using `GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (D.R.t + 1) true c c (G.parX j) (bigN D) (by omega) hne (isRegular_plus _) hcos hfar hcard hN (hgap _) (by rw [hpart]; exact hgap _)`. Rewrite `key` using `[hpart]`.

Conclude with `⟨D.R.t + 1, parXp D (j + 1) τ, parXp D j τ, rfl, rfl, Or.inr key⟩`.
-/
theorem pairPar_top : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (j : ℕ) (τ : D.what₂.Tau) (hj : j < D.R.m),
    PairPar (dualPar (parXp D (j + 1) τ)) (dualPar (parXp D j τ)) (-(D.hc τ).e ⟨j, hj⟩) (-(D.hc τ).e ⟨j, hj⟩) := by
  intro D hS j τ hj
  set G := grid D τ with hG
  have hj' : j + 1 ≤ D.R.m := hj
  have hce : (D.hc τ).e ⟨j, hj⟩ = ((G.e (j + 1) : ℤ) : ℚ) := by
    have := grid_e D τ (l := j + 1) (by omega) hj'
    simp only [Nat.add_sub_cancel] at this
    exact this.symm
  set c : ℚ := -(D.hc τ).e ⟨j, hj⟩ with hc
  have hblock : G.blockMPlus (j + 1) = TPar.block c (D.R.t + 1) := by
    rw [hc, hce]; rfl

  have habove : ∀ x ∈ G.weightX j, c + (D.R.t : ℚ) / 2 + 1 ≤ x := by
    intro x hx
    have htop : c + (D.R.t : ℚ) / 2 ∈ TPar.block c (D.R.t + 1) :=
      mem_block.2 ⟨0, by omega, by push_cast; ring⟩
    have hlt := grid_weightX_above D τ hj' hx (hblock ▸ htop)
    obtain ⟨z, hz⟩ := grid_inCoset_weightX D τ (j := j) x hx
    obtain ⟨u, hu⟩ := D.R.t_odd
    have ht : (D.R.t : ℚ) = 2 * u + 1 := by rw [hu]; push_cast; ring
    obtain ⟨w, hw⟩ : ∃ w : ℤ, c = w := ⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩
    rw [hz, hw, ht] at hlt ⊢
    have : (w : ℚ) + u < z := by linarith
    have h2 : w + u < z := by exact_mod_cast this
    have h3 : ((w + u + 1 : ℤ) : ℚ) ≤ z := by exact_mod_cast Int.add_one_le_iff.2 h2
    push_cast at h3
    linarith
  have hX : parXp D j τ = G.parX j := rfl
  have hX' : parXp D (j + 1) τ = G.parX (j + 1) := rfl
  have hpart : partner (D.R.t + 1) true c c (G.parX j) = G.parX (j + 1) := by
    unfold partner
    have h1 : ((G.parX j).image fun x : ℚ × Bool => (x.1 - c + c, if x.1 < c then !x.2 else x.2)) = G.parX j := by
      rw [← image_id (s := G.parX j)]
      rw [image_image]
      refine image_congr fun x hx => ?_
      have hx1 : x.1 ∈ G.weightX j := (mem_plus.1 hx).1
      have := habove _ hx1
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have hn : ¬ x.1 < c := by linarith
      simp [hn]
    rw [h1, GridData.parX, GridData.parX, GridData.weightX_succ, plus_union, hblock]
    rfl
  have hT : (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2 = (D.R.t : ℚ) / 2 + 1 := by push_cast; ring
  have hne : (G.parX j).Nonempty := by
    refine ⟨(G.a 0, true), mem_plus.2 ⟨GridData.mem_weightX.2 (Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)), rfl⟩⟩
  have hcos : InCoset (c + (((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (entries (G.parX j)) := by
    rw [GridData.parX, entries_plus, hT]
    intro x hx
    obtain ⟨z, hz⟩ := grid_inCoset_weightX D τ (j := j) x hx
    obtain ⟨u, hu⟩ := D.R.t_odd
    have ht : (D.R.t : ℚ) = 2 * u + 1 := by rw [hu]; push_cast; ring
    obtain ⟨w, hw⟩ : ∃ w : ℤ, c = w := ⟨-(G.e (j + 1)), by rw [hc, hce]; push_cast; ring⟩
    refine ⟨z - w - u - 1, ?_⟩
    rw [hz, hw, ht]; push_cast; ring
  have hfar : FarFrom c ((((D.R.t + 1 : ℕ) : ℚ) + 1) / 2) (G.parX j) := by
    rw [hT]
    intro x hx
    rw [GridData.parX, entries_plus] at hx
    have := habove x hx
    have h0 : (0 : ℚ) ≤ D.R.t := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcard : (G.parX j).card + (D.R.t + 1) ≤ bigN D := by
    rw [GridData.parX, ← (isRegular_plus _).card_entries, entries_plus]
    have := grid_card_weightX_le D τ j
    have e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
    have : (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hj'
    rw [e]
    nlinarith
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have e : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
    have : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Ranks.r at h1
    omega
  have hgap : ∀ E : Finset ℚ, GapOver (plus E) (2 * (bigN D : ℚ) ^ 3) := by
    intro E x hx y hy hxy
    exact absurd ((mem_plus.1 hx).2.trans (mem_plus.1 hy).2.symm) hxy
  have key := GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (D.R.t + 1) true c c (G.parX j) (bigN D) (by omega) hne (isRegular_plus _) hcos hfar hcard hN
    (hgap _) (by rw [hpart]; exact hgap _)
  rw [hpart] at key
  exact ⟨D.R.t + 1, parXp D (j + 1) τ, parXp D j τ, rfl, rfl, Or.inr key⟩

end GlobalTheory.TopPair
