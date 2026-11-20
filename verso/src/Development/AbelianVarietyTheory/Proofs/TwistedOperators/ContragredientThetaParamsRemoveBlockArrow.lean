import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.RemoveBlock
open GlobalTheory.SignedHC

/- English proof (translation)
Introduce `hx` and use `mem_shift.2 (by simpa using hx)`.
-/
theorem mem_shift' {h : ℚ} {S : SPar} {x : ℚ × Bool} : x ∈ S → (x.1 + h, x.2) ∈ shift h S := fun hx =>
  mem_shift.2 (by simpa using hx)

/- English proof (translation)
Introduce `x hx y hy hxy`. Use `H _ (mem_shift.1 hx) _ (mem_shift.1 hy) hxy` as an intermediate fact. Simplify using `using this`.
-/
theorem gapOver_shift {h d : ℚ} {S : SPar} (H : GapOver S d) : GapOver (shift h S) d := by
  intro x hx y hy hxy
  have := H _ (mem_shift.1 hx) _ (mem_shift.1 hy) hxy
  simpa using this

/- English proof (translation)
Introduce `x hx`. Take `⟨s, hs⟩` from `mem_entries.1 hx`. Use `H _ (fst_mem_entries (mem_shift.1 hs))` as an intermediate fact. Simplify using `only at this`. Use `this using 2` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem farFrom_shift {c h d : ℚ} {S : SPar} (H : FarFrom c d S) : FarFrom (c + h) d (shift h S) := by
  intro x hx
  obtain ⟨s, hs⟩ := mem_entries.1 hx
  have := H _ (fst_mem_entries (mem_shift.1 hs))
  simp only at this
  convert this using 2; ring

/- English proof (translation)
The claim follows from `Finset.card_image_of_injective _ fun x y e => Prod.ext (by simpa using congrArg Prod.fst e) (by simpa using congrArg Prod.snd e)`.
-/
theorem card_shift (h : ℚ) (S : SPar) : (shift h S).card = S.card :=
  Finset.card_image_of_injective _ fun x y e => Prod.ext (by simpa using congrArg Prod.fst e) (by simpa using congrArg Prod.snd e)

/- English proof (translation)
Introduce `x hx y hy e`. Assume the negation of the conclusion as `hne`. Use `H x hx y hy hne` as an intermediate fact. Rewrite `this` using `[e, sub_self, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isRegular_of_gapOver {S : SPar} {d : ℚ} (hd : 0 ≤ d) (H : GapOver S d) : IsRegular S := by
  intro x hx y hy e
  by_contra hne
  have := H x hx y hy hne
  rw [e, sub_self, abs_zero] at this
  linarith

/- English proof (translation)
Establish `ht` using `D.R.t_odd`. Establish `hk` using `D.R.k_even`. Establish `hm` using `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Establish `hr : Odd D.R.r`.

Take `⟨a, ha⟩` from `hk`. Take `⟨b, hb⟩` from `hm`. Conclude with `⟨a + b - 1, by unfold Ranks.r; omega⟩`. Establish `hs : Odd (sLen D)` using `by unfold sLen; exact hr.add_even (by decide)`. Unfold `rkV`.

Simplify using `only [Nat.odd_add, Nat.odd_mul, Nat.even_mul, ← Nat.not_odd_iff_even, hr, ht, hs, not_true, or_false, true_iff, iff_true]`. The claim follows by propositional logic.
-/
theorem odd_rkV (D : D7) (i j : ℕ) : Odd (rkV D i j) ↔ ¬ Odd (i + j) := by
  have ht := D.R.t_odd
  have hk := D.R.k_even
  have hm := D.R.m_even
  have h2 := D.R.two_le_m
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := hk; obtain ⟨b, hb⟩ := hm
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  have hs : Odd (sLen D) := by unfold sLen; exact hr.add_even (by decide)
  unfold rkV
  simp only [Nat.odd_add, Nat.odd_mul, Nat.even_mul, ← Nat.not_odd_iff_even, hr, ht, hs, not_true, or_false, true_iff,
    iff_true]
  tauto

section Facts
variable (D : D7) (τ : D.what₂.Tau)

/- English proof (translation)
Use `(GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.1 ⟨l - 1, by omega⟩` as an intermediate fact. Rewrite using `[this]`. Use `congr 2`. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((grid D τ).b l : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
  have := (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.1 ⟨l - 1, by omega⟩
  rw [this]; congr 2; simp only [Fin.val_mk]; omega

/- English proof (translation)
Use `(GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨l - 1, by omega⟩` as an intermediate fact. Rewrite using `[this]`. Use `congr 2`. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((grid D τ).e l : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
  have := (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨l - 1, by omega⟩
  rw [this]; congr 2; simp only [Fin.val_mk]; omega

/- English proof (translation)
Use `(GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).1 ⟨i - 2, by omega⟩` as an intermediate fact. Rewrite using `[this]`. Use `congr 2`. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : ((grid D τ).v i : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
  have := (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).1 ⟨i - 2, by omega⟩
  rw [this]; congr 2; simp only [Fin.val_mk]; omega

/- English proof (translation)
Rewrite using `[grid_e D τ h1 h2, grid_b D τ h1 h2]`. Conclude with `(D.hc τ).gap_be _`.
-/
theorem grid_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) :
    ((D.R.t : ℚ) + 3) / 2 ≤ (grid D τ).e l - (grid D τ).b l := by
  rw [grid_e D τ h1 h2, grid_b D τ h1 h2]; exact (D.hc τ).gap_be _

/- English proof (translation)
Rewrite using `[grid_e D τ h1 (by omega), grid_b D τ (by omega) h2]`. Use `(D.hc τ).gap_eb ⟨l - 1, by omega⟩ (by simp only; omega)` as an intermediate fact. Use `this using 4` and compare the differences between its conclusion and the goal. Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem grid_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) :
    ((D.R.t : ℚ) + 3) / 2 ≤ (grid D τ).b (l + 1) - (grid D τ).e l := by
  rw [grid_e D τ h1 (by omega), grid_b D τ (by omega) h2]
  have := (D.hc τ).gap_eb ⟨l - 1, by omega⟩ (by simp only; omega)
  convert this using 4; simp only; omega

/- English proof (translation)
Rewrite using `[grid_b D τ h1 (by omega), grid_b D τ (by omega) h2]`. Use `hS.2 τ (l - 1) (by omega)` as an intermediate fact. Apply the tactic sequence `convert this using 4 <;> (try simp only [Fin.mk.injEq]) <;> omega`.
-/
theorem grid_bb (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) :
    2 * (bigN D : ℚ) ^ 3 < (grid D τ).b (l + 1) - (grid D τ).b l := by
  rw [grid_b D τ h1 (by omega), grid_b D τ (by omega) h2]
  have := hS.2 τ (l - 1) (by omega)
  convert this using 4 <;> (try simp only [Fin.mk.injEq]) <;> omega

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt h`. Proceed by induction on `d with`. Consider the case `zero => have := grid_bb D τ hS h1 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ d ih`.

Use `ih (by omega) (by omega)` as an intermediate fact. Establish `h3` using `grid_bb D τ hS (l := l + d + 1) (by omega) (by omega)`. Establish `h4 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3` using `by positivity`. Rewrite using `[show l + (d + 1) + 1 = l + d + 1 + 1 by ring]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem grid_b_lt (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) :
    ((grid D τ).b l : ℚ) + 2 * (bigN D : ℚ) ^ 3 < (grid D τ).b l' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  induction d with
  | zero => have := grid_bb D τ hS h1 h2; linarith
  | succ d ih =>
    have := ih (by omega) (by omega)
    have h3 := grid_bb D τ hS (l := l + d + 1) (by omega) (by omega)
    have h4 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
    rw [show l + (d + 1) + 1 = l + d + 1 + 1 by ring]
    linarith

/- English proof (translation)
Break down `h.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `((grid D τ).b_mono l l' h1 h h2).le` after adjusting the coercions.
-/
theorem grid_b_le {l l' : ℕ} (h1 : 1 ≤ l) (h : l ≤ l') (h2 : l' ≤ D.R.m) :
    ((grid D τ).b l : ℚ) ≤ (grid D τ).b l' := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact_mod_cast ((grid D τ).b_mono l l' h1 h h2).le

/- English proof (translation)
Take `⟨i, hi2, hik, rfl⟩` from `GridData.mem_cloud.1 hx`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hvk : ((grid D τ).v D.R.k : ℚ) ≤ (grid D τ).v i`.

Break down `hik.eq_or_lt with h | h` into its components or cases. Conclude with `le_of_eq (by rw [h]; rfl)`. Conclude with `((grid D τ).v_anti i D.R.k hi2 h le_rfl).le` after adjusting the coercions. Use `lt_of_lt_of_le ?_ hvk` and prove the remaining obligations. Rewrite using `[grid_v D τ (by omega) le_rfl, grid_b D τ le_rfl (by omega)]`.

Establish `h1` using `(D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩`. Establish `h2` using `(D.hc τ).u_last_gt (by omega) (by omega)`. Establish `e1 : (⟨(⟨D.R.k - 2, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `Fin.ext (by simp only; omega)`. Rewrite `h1` using `[e1]`. Conclude with `h2.trans h1`.

Break down `hi2.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `((grid D τ).v_anti 2 i le_rfl h hik).le` after adjusting the coercions.
-/
theorem grid_cloud {x : ℚ} (hx : x ∈ (grid D τ).cloud) : -((grid D τ).b 1 : ℚ) < x ∧ x ≤ (grid D τ).v 2 := by
  obtain ⟨i, hi2, hik, rfl⟩ := GridData.mem_cloud.1 hx
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  refine ⟨?_, ?_⟩
  · have hvk : ((grid D τ).v D.R.k : ℚ) ≤ (grid D τ).v i := by
      rcases hik.eq_or_lt with h | h
      · exact le_of_eq (by rw [h]; rfl)
      · exact_mod_cast ((grid D τ).v_anti i D.R.k hi2 h le_rfl).le
    refine lt_of_lt_of_le ?_ hvk
    rw [grid_v D τ (by omega) le_rfl, grid_b D τ le_rfl (by omega)]
    have h1 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have h2 := (D.hc τ).u_last_gt (by omega) (by omega)
    have e1 : (⟨(⟨D.R.k - 2, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [e1] at h1
    exact h2.trans h1
  · rcases hi2.eq_or_lt with h | h
    · rw [← h]
    · exact_mod_cast ((grid D τ).v_anti 2 i le_rfl h hik).le

/- English proof (translation)
Establish `hb` using `GlobalTheory.SignedHC.abs_sub_le_of_mem_block hx`. Establish `hn` using `(grid_nearMid D τ) i (Finset.mem_Icc.2 ⟨h1, h2⟩)`. Rewrite `hn` using `[GridData.mid_eq _ h1]`. Establish `hg` using `(isLeast_gap D).1.2.1`. Establish `hg' : 2 * (bigN D : ℚ) ^ 3 + 2 * sLen D + 2 < gap D` using `by exact_mod_cast hg`.

Establish `ha : (grid D τ).a i = (grid D τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D)` using `rfl`. Establish `hi : (1 : ℚ) ≤ (D.R.m : ℚ) + 1 - i`. Establish `: (i : ℚ) ≤ D.R.m` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg0 : (0 : ℚ) ≤ gap D` using `by positivity`.

Establish `hs : ((grid D τ).s : ℚ) = sLen D` using `rfl`. Establish `hga : ((grid D τ).ga : ℚ) = gap D` using `rfl`. Rewrite `hb`, `hn` using `[abs_le]`. Rewrite `hb` using `[hs]`. Rewrite `hn` using `[hga]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem grid_blockC {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ (grid D τ).blockC i) :
    ((grid D τ).v 2 : ℚ) + 2 * (bigN D : ℚ) ^ 3 + sLen D < x := by
  have hb := GlobalTheory.SignedHC.abs_sub_le_of_mem_block hx
  have hn := (grid_nearMid D τ) i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  rw [GridData.mid_eq _ h1] at hn
  have hg := (isLeast_gap D).1.2.1
  have hg' : 2 * (bigN D : ℚ) ^ 3 + 2 * sLen D + 2 < gap D := by exact_mod_cast hg
  have ha : (grid D τ).a i = (grid D τ).v 2 + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D) := rfl
  have hi : (1 : ℚ) ≤ (D.R.m : ℚ) + 1 - i := by
    have : (i : ℚ) ≤ D.R.m := by exact_mod_cast h2
    linarith
  have hg0 : (0 : ℚ) ≤ gap D := by positivity
  have hs : ((grid D τ).s : ℚ) = sLen D := rfl
  have hga : ((grid D τ).ga : ℚ) = gap D := rfl
  rw [abs_le] at hb hn
  rw [hs] at hb
  rw [hga] at hn
  nlinarith

end Facts

/- English proof (translation)
Establish `hm` using `D.R.two_le_m`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hN : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3` using `by positivity`. Establish `hv2 : -((grid D τ).b 1 : ℚ) < (grid D τ).v 2` using `(grid_cloud D τ (GridData.mem_cloud.2 ⟨2, le_rfl, by show 2 ≤ D.R.k; omega, rfl⟩)).1`. Establish `key : ∀ x ∈ (grid D τ).parD i j, ∀ y ∈ (grid D τ).parD i j, x.2 = false → y.2 = true → 2 * (bigN D : ℚ) ^ 3 < y.1 - x.1 ∨ 2 * (bigN D : ℚ) ^ 3 < x.1 - y.1`.

Introduce `x hx y hy hxs hys`. Break down `GridData.mem_parD.1 hx with ⟨-, h⟩ | ⟨l, hl1, hlm, rfl⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩` into its components or cases. Rewrite using `[h] at hxs; exact absurd hxs (by decide)`. Use the proof step `swap; · rw [h] at hxs; exact absurd hxs (by decide)`. Use the proof step `swap; · rw [h] at hxs; exact absurd hxs (by decide)`.

Simplify using `only [decide_eq_false_iff_not, not_or, not_le] at hxs`. Take `⟨hlj, hev⟩` from `hxs`. Establish `hlm0 : l ≤ D.R.m` using `hlm`. Simplify using `only`. Establish `hb1 : ((grid D τ).b 1 : ℚ) + 2 * (bigN D : ℚ) ^ 3 < (grid D τ).b l` using `grid_b_lt D τ hS le_rfl (by omega) hlm`.

Break down `GridData.mem_parD.1 hy with ⟨hc, -⟩ | ⟨l', hl1', hlm', rfl⟩ | ⟨l', hl1', hlj', hM, -⟩ | ⟨l', hl1', hlm', hC, -⟩` into its components or cases. Use `left`. Use `(grid_cloud D τ hc).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only`.

Break down `lt_trichotomy l' l with h | rfl | h` into its components or cases. Use `left`. Use `grid_b_lt D τ hS hl1' h hlm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [decide_eq_true_eq] at hys`.

Break down `hys with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `absurd h hev`. Use `right`. Use `grid_b_lt D τ hS hl1 h hlm'` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `left`. Establish `hblk` using `GlobalTheory.SignedHC.abs_sub_le_of_mem_block hM`. Establish `heb` using `grid_eb D τ hl1' (l := l') (by omega)`. Establish `hbl` using `grid_b_lt D τ hS (l := l' + 1) (l' := l) (by omega) (by omega) hlm`.

Establish `ht : ((grid D τ).t : ℚ) = D.R.t` using `rfl`. Rewrite `hblk` using `[ht, abs_le]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `left`. Use `grid_blockC D τ (by omega) hlm' hC` as an intermediate fact.

Establish `hs : (0 : ℚ) ≤ sLen D` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx y hy hxy`. Apply the tactic sequence `cases hxs : x.2 <;> cases hys : y.2`. Conclude with `absurd (hxs.trans hys.symm) hxy`.

Break down `key x hx y hy hxs hys with h | h` into its components or cases. Rewrite using `[abs_sub_comm]`. Conclude with `h.trans_le (le_abs_self _)`. Conclude with `h.trans_le (le_abs_self _)`. Break down `key y hy x hx hys hxs with h | h` into its components or cases.

Conclude with `h.trans_le (le_abs_self _)`. Rewrite using `[abs_sub_comm]`. Conclude with `h.trans_le (le_abs_self _)`. Conclude with `absurd (hxs.trans hys.symm) hxy`.
-/
theorem gapOver_parD (D : D7) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (τ : D.what₂.Tau) (i j : ℕ) (hi : i ≤ D.R.m)
    (hj : j ≤ D.R.m) : GapOver ((grid D τ).parD i j) (2 * (bigN D : ℚ) ^ 3) := by
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hN : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hv2 : -((grid D τ).b 1 : ℚ) < (grid D τ).v 2 :=
    (grid_cloud D τ (GridData.mem_cloud.2 ⟨2, le_rfl, by show 2 ≤ D.R.k; omega, rfl⟩)).1

  have key : ∀ x ∈ (grid D τ).parD i j, ∀ y ∈ (grid D τ).parD i j, x.2 = false → y.2 = true →
      2 * (bigN D : ℚ) ^ 3 < y.1 - x.1 ∨ 2 * (bigN D : ℚ) ^ 3 < x.1 - y.1 := by
    intro x hx y hy hxs hys
    rcases GridData.mem_parD.1 hx with ⟨-, h⟩ | ⟨l, hl1, hlm, rfl⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩
    · rw [h] at hxs; exact absurd hxs (by decide)
    swap; · rw [h] at hxs; exact absurd hxs (by decide)
    swap; · rw [h] at hxs; exact absurd hxs (by decide)
    simp only [decide_eq_false_iff_not, not_or, not_le] at hxs
    obtain ⟨hlj, hev⟩ := hxs
    have hlm0 : l ≤ D.R.m := hlm
    simp only
    have hb1 : ((grid D τ).b 1 : ℚ) + 2 * (bigN D : ℚ) ^ 3 < (grid D τ).b l := grid_b_lt D τ hS le_rfl (by omega) hlm
    rcases GridData.mem_parD.1 hy with ⟨hc, -⟩ | ⟨l', hl1', hlm', rfl⟩ | ⟨l', hl1', hlj', hM, -⟩ | ⟨l', hl1', hlm', hC, -⟩
    · left; have := (grid_cloud D τ hc).1; linarith
    · simp only
      rcases lt_trichotomy l' l with h | rfl | h
      · left; have := grid_b_lt D τ hS hl1' h hlm; linarith
      · simp only [decide_eq_true_eq] at hys
        rcases hys with h | h
        · omega
        · exact absurd h hev
      · right; have := grid_b_lt D τ hS hl1 h hlm'; linarith
    · left
      have hblk := GlobalTheory.SignedHC.abs_sub_le_of_mem_block hM
      have heb := grid_eb D τ hl1' (l := l') (by omega)
      have hbl := grid_b_lt D τ hS (l := l' + 1) (l' := l) (by omega) (by omega) hlm
      have ht : ((grid D τ).t : ℚ) = D.R.t := rfl
      rw [ht, abs_le] at hblk
      linarith
    · left
      have := grid_blockC D τ (by omega) hlm' hC
      have hs : (0 : ℚ) ≤ sLen D := by positivity
      linarith
  intro x hx y hy hxy
  cases hxs : x.2 <;> cases hys : y.2
  · exact absurd (hxs.trans hys.symm) hxy
  · rcases key x hx y hy hxs hys with h | h
    · rw [abs_sub_comm]; exact h.trans_le (le_abs_self _)
    · exact h.trans_le (le_abs_self _)
  · rcases key y hy x hx hys hxs with h | h
    · exact h.trans_le (le_abs_self _)
    · rw [abs_sub_comm]; exact h.trans_le (le_abs_self _)
  · exact absurd (hxs.trans hys.symm) hxy

section Side
variable (D : D7) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m)
include hj

/- English proof (translation)
Use `grid_eb D τ (l := j + 1) (by omega) (by omega)` as an intermediate fact. Use `grid_b_le D τ (l := j + 2) (l' := l) (by omega) h1 h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem low_below {l : ℕ} (h1 : j + 2 ≤ l) (h2 : l ≤ D.R.m) :
    -((grid D τ).b l : ℚ) + ((D.R.t : ℚ) + 3) / 2 ≤ -((grid D τ).e (j + 1) : ℚ) := by
  have := grid_eb D τ (l := j + 1) (by omega) (by omega)
  have := grid_b_le D τ (l := j + 2) (l' := l) (by omega) h1 h2
  linarith

/- English proof (translation)
Use `grid_be D τ (l := j + 1) (by omega) (by omega)` as an intermediate fact. Use `grid_b_le D τ h1 h2 (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem low_above {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ j + 1) :
    -((grid D τ).e (j + 1) : ℚ) + ((D.R.t : ℚ) + 3) / 2 ≤ -((grid D τ).b l : ℚ) := by
  have := grid_be D τ (l := j + 1) (by omega) (by omega)
  have := grid_b_le D τ h1 h2 (by omega)
  linarith

/- English proof (translation)
Use `(grid_cloud D τ hx).1` as an intermediate fact. Use `low_above D τ hj (l := 1) le_rfl (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_above {x : ℚ} (hx : x ∈ (grid D τ).cloud) :
    -((grid D τ).e (j + 1) : ℚ) + ((D.R.t : ℚ) + 3) / 2 < x := by
  have := (grid_cloud D τ hx).1
  have := low_above D τ hj (l := 1) le_rfl (by omega)
  linarith

/- English proof (translation)
Establish `hblk` using `GlobalTheory.SignedHC.abs_sub_le_of_mem_block hx`. Establish `ht : ((grid D τ).t : ℚ) = D.R.t` using `rfl`. Rewrite `hblk` using `[ht, abs_le]`. Use `grid_eb D τ h1 (l := l) (by omega)` as an intermediate fact. Use `low_above D τ hj (l := l + 1) (by omega) (by omega)` as an intermediate fact.

Establish `: (0 : ℚ) ≤ D.R.t` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem blockM_above {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ j) {x : ℚ} (hx : x ∈ (grid D τ).blockM l) :
    -((grid D τ).e (j + 1) : ℚ) + ((D.R.t : ℚ) + 3) / 2 < x := by
  have hblk := GlobalTheory.SignedHC.abs_sub_le_of_mem_block hx
  have ht : ((grid D τ).t : ℚ) = D.R.t := rfl
  rw [ht, abs_le] at hblk
  have := grid_eb D τ h1 (l := l) (by omega)
  have := low_above D τ hj (l := l + 1) (by omega) (by omega)
  have : (0 : ℚ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Use `grid_blockC D τ h1 h2 hx` as an intermediate fact. Use `cloud_above D τ hj (x := (grid D τ).v 2) (GridData.mem_cloud.2 ⟨2, le_rfl, by` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Use `show 2 ≤ D.R.k`. Use the proof step `omega, rfl⟩)`.

Establish `: (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 + sLen D` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem blockC_above {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) {x : ℚ} (hx : x ∈ (grid D τ).blockC l) :
    -((grid D τ).e (j + 1) : ℚ) + ((D.R.t : ℚ) + 3) / 2 < x := by
  have := grid_blockC D τ h1 h2 hx
  have := cloud_above D τ hj (x := (grid D τ).v 2) (GridData.mem_cloud.2 ⟨2, le_rfl, by
    have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩)
  have : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 + sLen D := by positivity
  linarith

end Side

/- English proof (translation)
Introduce `x hx`. Take `⟨s, hs⟩` from `mem_entries.1 hx`. Break down `GridData.mem_parD.1 hs with ⟨h, -⟩ | ⟨l, hl1, hlm, e⟩ | ⟨l, hl1, hlj, h, -⟩ | ⟨l, hl1, hlm, h, -⟩` into its components or cases. Use `cloud_above D τ hj h; rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith` as an intermediate fact. Establish `hx' : x = -((grid D τ).b l : ℚ)` using `congrArg Prod.fst e`.

Establish `hlm0 : l ≤ D.R.m` using `hlm`. Rewrite using `[hx']`. Break down `le_or_gt l (j + 1) with h | h` into its components or cases. Use `low_above D τ hj hl1 h` as an intermediate fact. Rewrite using `[abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith`.

Use `low_below D τ hj (l := l) (by omega) hlm0` as an intermediate fact. Rewrite using `[abs_of_neg (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith`. Use `blockM_above D τ hj hl1 hlj h; rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith` as an intermediate fact. Use `blockC_above D τ hj (by omega) hlm h` as an intermediate fact. Rewrite using `[abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith`.
-/
theorem farFrom_parD (D : D7) (τ : D.what₂.Tau) (i j : ℕ) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    FarFrom (-((grid D τ).e (j + 1) : ℚ)) (((D.R.t : ℚ) + 3) / 2) ((grid D τ).parD i j) := by
  intro x hx
  obtain ⟨s, hs⟩ := mem_entries.1 hx
  rcases GridData.mem_parD.1 hs with ⟨h, -⟩ | ⟨l, hl1, hlm, e⟩ | ⟨l, hl1, hlj, h, -⟩ | ⟨l, hl1, hlm, h, -⟩
  · have := cloud_above D τ hj h; rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith
  · have hx' : x = -((grid D τ).b l : ℚ) := congrArg Prod.fst e
    have hlm0 : l ≤ D.R.m := hlm
    rw [hx']
    rcases le_or_gt l (j + 1) with h | h
    · have := low_above D τ hj hl1 h
      rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith
    · have := low_below D τ hj (l := l) (by omega) hlm0
      rw [abs_of_neg (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith
  · have := blockM_above D τ hj hl1 hlj h; rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith
  · have := blockC_above D τ hj (by omega) hlm h
    rw [abs_of_pos (by linarith [show (0:ℚ) ≤ D.R.t by positivity])]; linarith

/- English proof (translation)
Use extensionality with `⟨a, s⟩`. Rewrite using `[mem_shift, mem_liftPlus]`. Simplify using `only [partner, Finset.mem_union, Finset.mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨⟨z, σ⟩, hz, h1, h2⟩ | ⟨y, hy, rfl, rfl⟩)`.

Apply the tactic sequence `try simp only at h1 h2`. Establish `ha : a - (c' - c) = z` using `by linarith`. Rewrite using `[ha]`. Distinguish the cases in `hzc : z < c`. Rewrite `h2` using `[if_pos hzc]`.

Substitute `h2` using the available equality. Conclude with `Or.inr (Or.inl ⟨hzc, by simpa using hz⟩)`. Rewrite `h2` using `[if_neg hzc]`. Substitute `h2` using the available equality. Conclude with `Or.inl ⟨not_lt.1 hzc, hz⟩`.

Apply the tactic sequence `refine Or.inr (Or.inr ⟨?_, rfl⟩) try simp only`. Rewrite using `[sub_mem_block, show c + (c' - c) = c' by ring]; exact hy`. Introduce and unpack `(⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)`. Apply the tactic sequence `try simp only at h1 h2`. Apply the tactic sequence `exact Or.inl ⟨(a - (c' - c), s), h2, by (try simp only); ring, by (try simp only); rw [if_neg (not_lt.2 h1)]⟩`.

Apply the tactic sequence `try simp only at h1 h2`. Apply the tactic sequence `exact Or.inl ⟨(a - (c' - c), !s), h2, by (try simp only); ring, by (try simp only); rw [if_pos h1, Bool.not_not]⟩`. Apply the tactic sequence `try simp only at h1 h2`. Rewrite `h1` using `[sub_mem_block, show c + (c' - c) = c' by ring]`. Conclude with `Or.inr ⟨a, h1, rfl, h2.symm⟩`.
-/
theorem partner_true_eq (t : ℕ) (c c' : ℚ) (P : SPar) : partner t true c c' P = shift (c' - c) (liftPlus c t P) := by
  ext ⟨a, s⟩
  rw [mem_shift, mem_liftPlus]
  simp only [partner, Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨z, σ⟩, hz, h1, h2⟩ | ⟨y, hy, rfl, rfl⟩)
    · try simp only at h1 h2
      have ha : a - (c' - c) = z := by linarith
      rw [ha]
      by_cases hzc : z < c
      · rw [if_pos hzc] at h2; subst h2
        exact Or.inr (Or.inl ⟨hzc, by simpa using hz⟩)
      · rw [if_neg hzc] at h2; subst h2
        exact Or.inl ⟨not_lt.1 hzc, hz⟩
    · refine Or.inr (Or.inr ⟨?_, rfl⟩)
      try simp only
      rw [sub_mem_block, show c + (c' - c) = c' by ring]; exact hy
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · try simp only at h1 h2
      exact Or.inl ⟨(a - (c' - c), s), h2, by (try simp only); ring, by (try simp only); rw [if_neg (not_lt.2 h1)]⟩
    · try simp only at h1 h2
      exact Or.inl ⟨(a - (c' - c), !s), h2, by (try simp only); ring, by (try simp only); rw [if_pos h1, Bool.not_not]⟩
    · try simp only at h1 h2
      rw [sub_mem_block, show c + (c' - c) = c' by ring] at h1
      exact Or.inr ⟨a, h1, rfl, h2.symm⟩

/- English proof (translation)
Establish `ht0 : (0 : ℚ) ≤ D.R.t` using `by positivity`. Use extensionality with `⟨a, s⟩`. Rewrite using `[mem_liftPlus, GridData.mem_parD, GridData.mem_parD, GridData.mem_parD]`. Apply the tactic sequence `try simp only`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(⟨h, rfl⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, rfl⟩ | ⟨l, hl1, hlm, h, rfl⟩)`. Conclude with `Or.inl ⟨by linarith [cloud_above D τ hj h], Or.inl ⟨h, rfl⟩⟩`. Take `⟨rfl, rfl⟩` from `Prod.mk.injEq _ _ _ _ ▸ he`. Establish `hlm0 : l ≤ D.R.m` using `hlm`. Break down `le_or_gt l (j + 1) with h | h` into its components or cases.

Use `Or.inl ⟨by linarith [low_above D τ hj hl1 h], Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)⟩` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq, true_and]`. Simplify using `[h, show l ≤ j + 1 + 1 by omega]`. Use `Or.inr (Or.inl ⟨by linarith [low_below D τ hj (l := l) (by omega) hlm0], Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)⟩)` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq, true_and]`.

Establish `e1 : l - j - 1 = (l - (j + 1) - 1) + 1` using `by omega`. Simplify using `only [e1, Nat.even_add_one]`. Distinguish the cases in `hl : l ≤ j + 1 + 1`. Establish `e2 : l - (j + 1) - 1 = 0` using `by omega`. Simplify using `[hl, e2, show ¬ l ≤ j + 1 by omega]`.

Simplify using `[hl, show ¬ l ≤ j + 1 by omega, ← Nat.not_even_iff_odd]`. Break down `(Nat.lt_or_eq_of_le hlj) with h' | h'` into its components or cases. Conclude with `Or.inl ⟨by linarith [blockM_above D τ hj hl1 (by omega) h], Or.inr (Or.inr (Or.inl ⟨l, hl1, by omega, h, rfl⟩))⟩`. Substitute `h'` using the available equality. Conclude with `Or.inr (Or.inr ⟨h, rfl⟩)`.

Conclude with `Or.inl ⟨by linarith [blockC_above D τ hj (by omega) hlm h], Or.inr (Or.inr (Or.inr ⟨l, hl1, hlm, h, rfl⟩))⟩`. Introduce and unpack `(⟨hc, h⟩ | ⟨hc, h⟩ | ⟨h, rfl⟩)`. Break down `h with ⟨h, rfl⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, rfl⟩ | ⟨l, hl1, hlm, h, rfl⟩` into its components or cases. Conclude with `Or.inl ⟨h, rfl⟩`. Take `⟨rfl, rfl⟩` from `Prod.mk.injEq _ _ _ _ ▸ he`.

Establish `hlm0 : l ≤ D.R.m` using `hlm`. Establish `h : l ≤ j + 1`. Assume the negation of the conclusion as `h`. Use `low_below D τ hj (l := l) (by omega) hlm0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq, true_and]`. Simplify using `[h, show l ≤ j + 1 + 1 by omega]`. Conclude with `Or.inr (Or.inr (Or.inl ⟨l, hl1, by omega, h, rfl⟩))`. Conclude with `Or.inr (Or.inr (Or.inr ⟨l, hl1, hlm, h, rfl⟩))`.

Break down `h with ⟨h, -⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, -⟩ | ⟨l, hl1, hlm, h, -⟩` into its components or cases. Combine the linear relations using `[cloud_above D τ hj h]`. Simplify using `only [Prod.mk.injEq] at he`. Take `⟨ha, hs⟩` from `he`. Substitute `ha` using the available equality.

Establish `hlm0 : l ≤ D.R.m` using `hlm`. Establish `h : ¬ l ≤ j + 1`. Introduce `h`. Use `low_above D τ hj hl1 h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)` and prove the remaining obligations. Simplify using `only [Prod.mk.injEq, true_and]`. Establish `hs' : s = !decide (l ≤ j + 1 ∨ Even (l - j - 1))` using `by rw [← hs, Bool.not_not]`. Rewrite using `[hs']`. Establish `e1 : l - j - 1 = (l - (j + 1) - 1) + 1` using `by omega`.

Simplify using `only [e1, Nat.even_add_one]`. Distinguish the cases in `hl : l ≤ j + 1 + 1`. Establish `e2 : l - (j + 1) - 1 = 0` using `by omega`. Simplify using `[hl, e2, h]`. Simplify using `[hl, h, ← Nat.not_even_iff_odd]`.

Combine the linear relations using `[blockM_above D τ hj hl1 hlj h]`. Combine the linear relations using `[blockC_above D τ hj (by omega) hlm h]`. Conclude with `Or.inr (Or.inr (Or.inl ⟨j + 1, by omega, le_rfl, h, rfl⟩))`.
-/
theorem parD_succ (D : D7) (τ : D.what₂.Tau) (i j : ℕ) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    (grid D τ).parD i (j + 1) = liftPlus (-((grid D τ).e (j + 1) : ℚ)) D.R.t ((grid D τ).parD i j) := by
  have ht0 : (0 : ℚ) ≤ D.R.t := by positivity
  ext ⟨a, s⟩
  rw [mem_liftPlus, GridData.mem_parD, GridData.mem_parD, GridData.mem_parD]
  try simp only
  constructor
  · rintro (⟨h, rfl⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, rfl⟩ | ⟨l, hl1, hlm, h, rfl⟩)
    · exact Or.inl ⟨by linarith [cloud_above D τ hj h], Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ he
      have hlm0 : l ≤ D.R.m := hlm
      rcases le_or_gt l (j + 1) with h | h
      · refine Or.inl ⟨by linarith [low_above D τ hj hl1 h], Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)⟩
        simp only [Prod.mk.injEq, true_and]
        simp [h, show l ≤ j + 1 + 1 by omega]
      · refine Or.inr (Or.inl ⟨by linarith [low_below D τ hj (l := l) (by omega) hlm0], Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)⟩)
        simp only [Prod.mk.injEq, true_and]
        have e1 : l - j - 1 = (l - (j + 1) - 1) + 1 := by omega
        simp only [e1, Nat.even_add_one]
        by_cases hl : l ≤ j + 1 + 1
        · have e2 : l - (j + 1) - 1 = 0 := by omega
          simp [hl, e2, show ¬ l ≤ j + 1 by omega]
        · simp [hl, show ¬ l ≤ j + 1 by omega, ← Nat.not_even_iff_odd]
    · rcases (Nat.lt_or_eq_of_le hlj) with h' | h'
      · exact Or.inl ⟨by linarith [blockM_above D τ hj hl1 (by omega) h], Or.inr (Or.inr (Or.inl ⟨l, hl1, by omega, h, rfl⟩))⟩
      · subst h'; exact Or.inr (Or.inr ⟨h, rfl⟩)
    · exact Or.inl ⟨by linarith [blockC_above D τ hj (by omega) hlm h], Or.inr (Or.inr (Or.inr ⟨l, hl1, hlm, h, rfl⟩))⟩
  · rintro (⟨hc, h⟩ | ⟨hc, h⟩ | ⟨h, rfl⟩)
    · rcases h with ⟨h, rfl⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, rfl⟩ | ⟨l, hl1, hlm, h, rfl⟩
      · exact Or.inl ⟨h, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ he
        have hlm0 : l ≤ D.R.m := hlm
        have h : l ≤ j + 1 := by
          by_contra h
          have := low_below D τ hj (l := l) (by omega) hlm0
          linarith
        refine Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)
        simp only [Prod.mk.injEq, true_and]
        simp [h, show l ≤ j + 1 + 1 by omega]
      · exact Or.inr (Or.inr (Or.inl ⟨l, hl1, by omega, h, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨l, hl1, hlm, h, rfl⟩))
    · rcases h with ⟨h, -⟩ | ⟨l, hl1, hlm, he⟩ | ⟨l, hl1, hlj, h, -⟩ | ⟨l, hl1, hlm, h, -⟩
      · linarith [cloud_above D τ hj h]
      · simp only [Prod.mk.injEq] at he
        obtain ⟨ha, hs⟩ := he
        subst ha
        have hlm0 : l ≤ D.R.m := hlm
        have h : ¬ l ≤ j + 1 := by
          intro h
          have := low_above D τ hj hl1 h
          linarith
        refine Or.inr (Or.inl ⟨l, hl1, hlm, ?_⟩)
        simp only [Prod.mk.injEq, true_and]
        have hs' : s = !decide (l ≤ j + 1 ∨ Even (l - j - 1)) := by rw [← hs, Bool.not_not]
        rw [hs']
        have e1 : l - j - 1 = (l - (j + 1) - 1) + 1 := by omega
        simp only [e1, Nat.even_add_one]
        by_cases hl : l ≤ j + 1 + 1
        · have e2 : l - (j + 1) - 1 = 0 := by omega
          simp [hl, e2, h]
        · simp [hl, h, ← Nat.not_even_iff_odd]
      · linarith [blockM_above D τ hj hl1 hlj h]
      · linarith [blockC_above D τ hj (by omega) hlm h]
    · exact Or.inr (Or.inr (Or.inl ⟨j + 1, by omega, le_rfl, h, rfl⟩))

/- English proof (translation)
Establish `hl : liftPlus (-((grid D τ).e (j + 1) : ℚ) + h) D.R.t (shift h ((grid D τ).parD i j)) = shift h (liftPlus (-((grid D τ).e (j + 1) : ℚ)) D.R.t ((grid D τ).parD i j))` using `lift_shift .pos _ h D.R.t _`. Establish `hss : ∀ (a b : ℚ) (S : SPar), shift a (shift b S) = shift (b + a) S`. Introduce `a b S`. Use extensionality with `x`. Simplify using `only [mem_shift]`.

Put the polynomial expressions in normal form. Rewrite using `[partner_true_eq, hl, parD_succ D τ i j hi hj, hss]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem partner_parD (D : D7) (τ : D.what₂.Tau) (i j : ℕ) (hi : i ≤ D.R.m) (hj : j < D.R.m) (h h' : ℚ) :
    shift h' ((grid D τ).parD i (j + 1)) =
      partner D.R.t true (-((grid D τ).e (j + 1) : ℚ) + h) (-((grid D τ).e (j + 1) : ℚ) + h')
        (shift h ((grid D τ).parD i j)) := by
  have hl : liftPlus (-((grid D τ).e (j + 1) : ℚ) + h) D.R.t (shift h ((grid D τ).parD i j)) =
      shift h (liftPlus (-((grid D τ).e (j + 1) : ℚ)) D.R.t ((grid D τ).parD i j)) :=
    lift_shift .pos _ h D.R.t _
  have hss : ∀ (a b : ℚ) (S : SPar), shift a (shift b S) = shift (b + a) S := by
    intro a b S; ext x; simp only [mem_shift]; ring_nf
  rw [partner_true_eq, hl, parD_succ D τ i j hi hj, hss]
  congr 1; ring

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hc : (plus (grid D τ).cloud).card ≤ D.R.k - 1` using `Finset.card_image_le.trans (Finset.card_image_le.trans (by simp only [Nat.card_Icc]; show D.R.k + 1 - 2 ≤ _; omega))`. Establish `hl : ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),`. Use `decide (l ≤ j + 1 ∨ Even (l - j - 1)))).card ≤ D.R.m :=`. Use the proof step `Finset.card_image_le.trans (by simp only [Nat.card_Icc]; show D.R.m + 1 - 1 ≤ _; omega)`.

Establish `hM : (plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM)).card ≤ j * D.R.t`. Use `Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)` and prove the remaining obligations. Simplify using `only [GridData.blockM, card_block, Finset.sum_const, Nat.card_Icc, smul_eq_mul]`. Use `show (j + 1 - 1) * D.R.t ≤ _`. Simplify using the standard rewrite rules.

Establish `hC : (plus ((Finset.Icc ((grid D τ).m - i + 1) (grid D τ).m).biUnion (grid D τ).blockC)).card ≤ i * sLen D`. Use `Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)` and prove the remaining obligations. Simplify using `only [GridData.blockC, card_block, Finset.sum_const, Nat.card_Icc, smul_eq_mul]`. Use `show (D.R.m + 1 - (D.R.m - i + 1)) * sLen D ≤ _`. Rewrite using `[show D.R.m + 1 - (D.R.m - i + 1) = i by omega]`.

Unfold `GridData.parD`. Establish `u1` using `Finset.card_union_le (plus (grid D τ).cloud ∪ ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),`. Use `decide (l ≤ j + 1 ∨ Even (l - j - 1)))) ∪ plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM))`. Use the proof step `(plus ((Finset.Icc ((grid D τ).m - i + 1) (grid D τ).m).biUnion (grid D τ).blockC))`. Establish `u2` using `Finset.card_union_le (plus (grid D τ).cloud ∪ ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),`.

Use `decide (l ≤ j + 1 ∨ Even (l - j - 1))))) (plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM))`. Establish `u3` using `Finset.card_union_le (plus (grid D τ).cloud) ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),`. Use `decide (l ≤ j + 1 ∨ Even (l - j - 1))))`. Unfold `rkV Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_parD_le (D : D7) (τ : D.what₂.Tau) (i j : ℕ) (hi : i ≤ D.R.m) : ((grid D τ).parD i j).card ≤ rkV D i j := by
  have hk := D.R.m_add_three_le_k
  have hc : (plus (grid D τ).cloud).card ≤ D.R.k - 1 :=
    Finset.card_image_le.trans (Finset.card_image_le.trans (by simp only [Nat.card_Icc]; show D.R.k + 1 - 2 ≤ _; omega))
  have hl : ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),
      decide (l ≤ j + 1 ∨ Even (l - j - 1)))).card ≤ D.R.m :=
    Finset.card_image_le.trans (by simp only [Nat.card_Icc]; show D.R.m + 1 - 1 ≤ _; omega)
  have hM : (plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM)).card ≤ j * D.R.t := by
    refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
    simp only [GridData.blockM, card_block, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    show (j + 1 - 1) * D.R.t ≤ _
    simp
  have hC : (plus ((Finset.Icc ((grid D τ).m - i + 1) (grid D τ).m).biUnion (grid D τ).blockC)).card ≤ i * sLen D := by
    refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
    simp only [GridData.blockC, card_block, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    show (D.R.m + 1 - (D.R.m - i + 1)) * sLen D ≤ _
    rw [show D.R.m + 1 - (D.R.m - i + 1) = i by omega]
  unfold GridData.parD
  have u1 := Finset.card_union_le (plus (grid D τ).cloud ∪ ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),
      decide (l ≤ j + 1 ∨ Even (l - j - 1)))) ∪ plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM))
    (plus ((Finset.Icc ((grid D τ).m - i + 1) (grid D τ).m).biUnion (grid D τ).blockC))
  have u2 := Finset.card_union_le (plus (grid D τ).cloud ∪ ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),
      decide (l ≤ j + 1 ∨ Even (l - j - 1))))) (plus ((Finset.Icc 1 j).biUnion (grid D τ).blockM))
  have u3 := Finset.card_union_le (plus (grid D τ).cloud) ((Finset.Icc 1 (grid D τ).m).image fun l => (-((grid D τ).b l : ℚ),
      decide (l ≤ j + 1 ∨ Even (l - j - 1))))
  unfold rkV Ranks.r
  omega

/- English proof (translation)
Establish `hr : Odd D.R.r`. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Conclude with `⟨a + b - 1, by unfold Ranks.r; omega⟩`.

Establish `hblk : ∀ (c : ℤ) (n : ℕ), Odd n → ∀ x ∈ TPar.block (c : ℚ) n, ∃ z : ℤ, x = z`. Introduce `c n hn x hx`. Take `⟨q, rfl⟩` from `hn`. Take `⟨a, -, rfl⟩` from `mem_block.1 hx`. Conclude with `⟨c + q - a, by push_cast; ring⟩`.

Introduce `x hx`. Take `⟨s, hs⟩` from `mem_entries.1 hx`. Break down `GridData.mem_parD.1 hs with ⟨h, -⟩ | ⟨l, -, -, e⟩ | ⟨l, -, -, h, -⟩ | ⟨l, -, -, h, -⟩` into its components or cases. Take `⟨i, -, -, rfl⟩` from `GridData.mem_cloud.1 h`. Conclude with `⟨_, rfl⟩`.

Establish `e1` using `congrArg Prod.fst e`. Simplify using `only at e1`. Conclude with `⟨-(grid D τ).b l, by rw [e1]; push_cast; ring⟩`. Conclude with `hblk (-(grid D τ).e l) (grid D τ).t D.R.t_odd x (by simpa [GridData.blockM] using h)`. Conclude with `hblk ((grid D τ).cen l) (grid D τ).s (show Odd (sLen D) by unfold sLen; exact hr.add_even (by decide)) x h`.
-/
theorem int_parD (D : D7) (τ : D.what₂.Tau) (i j : ℕ) : ∀ x ∈ entries ((grid D τ).parD i j), ∃ z : ℤ, x = z := by
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even; obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  have hblk : ∀ (c : ℤ) (n : ℕ), Odd n → ∀ x ∈ TPar.block (c : ℚ) n, ∃ z : ℤ, x = z := by
    intro c n hn x hx
    obtain ⟨q, rfl⟩ := hn
    obtain ⟨a, -, rfl⟩ := mem_block.1 hx
    exact ⟨c + q - a, by push_cast; ring⟩
  intro x hx
  obtain ⟨s, hs⟩ := mem_entries.1 hx
  rcases GridData.mem_parD.1 hs with ⟨h, -⟩ | ⟨l, -, -, e⟩ | ⟨l, -, -, h, -⟩ | ⟨l, -, -, h, -⟩
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloud.1 h; exact ⟨_, rfl⟩
  · have e1 := congrArg Prod.fst e
    simp only at e1
    exact ⟨-(grid D τ).b l, by rw [e1]; push_cast; ring⟩
  · exact hblk (-(grid D τ).e l) (grid D τ).t D.R.t_odd x (by simpa [GridData.blockM] using h)
  · exact hblk ((grid D τ).cen l) (grid D τ).s (show Odd (sLen D) by unfold sLen; exact hr.add_even (by decide)) x h

/- English proof (translation)
Introduce `D hS i j τ hi hj`. Establish `he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ)` using `(GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩`. Use `set G := grid D τ with hG`. Use `set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ`. Use `set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'`.

Establish `hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ`. Simplify using `only [att, he, hδ]`. Distinguish the cases in `h : Odd (i + j)`. Establish `h' : Odd (rkV D i (j + 1))` using `by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto`. Simplify using `only [h, h', if_true]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ Odd (rkV D i (j + 1))` using `by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto`. Simplify using `only [h, h', if_false]`. Expand and normalize the polynomial expressions, which then agree. Establish `hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ'`.

Simplify using `only [att, he, hδ']`. Distinguish the cases in `h : Odd (i + j)`. Establish `h' : Odd (rkV D i j) ↔ False` using `by rw [odd_rkV]; tauto`. Establish `h'' : Odd (i + (j + 1)) ↔ False` using `by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto`. Simplify using `only [h', h'', if_false]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h' : Odd (rkV D i j)` using `by rw [odd_rkV]; tauto`. Establish `h'' : Odd (i + (j + 1))` using `by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto`. Simplify using `only [h', h'', if_true]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hT, hS']`. Use `set P := shift δ (G.parD i j) with hP`. Establish `hpart` using `partner_parD D τ i j hi hj δ δ'`. Establish `ht : 1 ≤ D.R.t` using `D.R.t_odd.pos`. Establish `hN : 1800 < bigN D`.

Establish `h1` using `hS.1`. Establish `h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1)` using `Nat.le_mul_of_pos_right _ (by omega)`. Unfold `bigN`. Unfold `Ranks.r at h1`. Use linear arithmetic over natural numbers and integers.

Establish `hgap : GapOver P (2 * (bigN D : ℚ) ^ 3)` using `gapOver_shift (gapOver_parD D hS τ i j hi hj.le)`. Establish `hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P) (2 * (bigN D : ℚ) ^ 3)`. Rewrite using `[hP, ← hpart]`. Conclude with `gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)`. Establish `hreg : IsRegular P` using `isRegular_of_gapOver (by positivity) hgap`.

Establish `hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P` using `farFrom_shift (farFrom_parD D τ i j hi hj)`. Establish `hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P` using `fun x hx => le_trans (by linarith) (hfar3 x hx)`. Establish `hne : P.Nonempty`. Establish `hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud` using `GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩`. Establish `hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j` using `GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)`.

Conclude with `⟨_, mem_shift' hmem⟩`. Establish `hcard : P.card + D.R.t ≤ bigN D`. Rewrite using `[hP, card_shift]`. Establish `h0 : (G.parD i j).card ≤ rkV D i j` using `card_parD_le D τ i j hi`. Establish `a : (j + 1) * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ hj`.

Establish `b : i * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ hi`. Establish `c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m` using `by ring`. Establish `d : (j + 1) * D.R.t = j * D.R.t + D.R.t` using `by ring`. Use `show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Unfold `rkV Ranks.r at h0`.

Use linear arithmetic over natural numbers and integers. Establish `hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (entries P)`. Introduce `x hx`. Take `⟨s, hs⟩` from `mem_entries.1 hx`. Establish `hy` using `fst_mem_entries (mem_shift.1 hs)`.

Take `⟨z, hz⟩` from `int_parD D τ i j _ hy`. Simplify using `only at hz`. Take `⟨q, hq⟩` from `D.R.t_odd`. Establish `htq : ((D.R.t : ℚ) + 1) / 2 = q + 1` using `by rw [hq]; push_cast; ring`. Use `⟨z + G.e (j + 1) - (q + 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[htq]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨D.R.t, P, partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P, rfl, ?_, Or.inl ⟨?_, hfar3⟩⟩` and prove the remaining obligations. Rewrite using `[parV, ← hpart]`.

Conclude with `GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'`.
-/
theorem removeBlock_pairPar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i ≤ D.R.m → ∀ hj : j < D.R.m,
    PairPar (parV D i j τ) (parV D i (j + 1) τ) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j))
      (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1))) := by
  intro D hS i j τ hi hj
  have he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩
  set G := grid D τ with hG
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'
  have hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ := by
    simp only [att, he, hδ]
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_true]; ring
    · have h' : ¬ Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_false]; ring
  have hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ' := by
    simp only [att, he, hδ']
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i j) ↔ False := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) ↔ False := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_false]; ring
    · have h' : Odd (rkV D i j) := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_true]; ring
  rw [hT, hS']
  set P := shift δ (G.parD i j) with hP
  have hpart := partner_parD D τ i j hi hj δ δ'
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold bigN; unfold Ranks.r at h1
    omega
  have hgap : GapOver P (2 * (bigN D : ℚ) ^ 3) := gapOver_shift (gapOver_parD D hS τ i j hi hj.le)
  have hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P)
      (2 * (bigN D : ℚ) ^ 3) := by
    rw [hP, ← hpart]; exact gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)
  have hreg : IsRegular P := isRegular_of_gapOver (by positivity) hgap
  have hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P := farFrom_shift (farFrom_parD D τ i j hi hj)
  have hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P := fun x hx =>
    le_trans (by linarith) (hfar3 x hx)
  have hne : P.Nonempty := by
    have hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud :=
      GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩
    have hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j := GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)
    exact ⟨_, mem_shift' hmem⟩
  have hcard : P.card + D.R.t ≤ bigN D := by
    rw [hP, card_shift]
    have h0 : (G.parD i j).card ≤ rkV D i j := card_parD_le D τ i j hi
    have a : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have b : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    have d : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
    show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    unfold rkV Ranks.r at h0
    omega
  have hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (entries P) := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    have hy := fst_mem_entries (mem_shift.1 hs)
    obtain ⟨z, hz⟩ := int_parD D τ i j _ hy
    simp only at hz
    obtain ⟨q, hq⟩ := D.R.t_odd
    have htq : ((D.R.t : ℚ) + 1) / 2 = q + 1 := by rw [hq]; push_cast; ring
    refine ⟨z + G.e (j + 1) - (q + 1), ?_⟩
    rw [htq]; push_cast; linarith
  refine ⟨D.R.t, P, partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P, rfl, ?_, Or.inl ⟨?_, hfar3⟩⟩
  · rw [parV, ← hpart]
  · exact GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'

end GlobalTheory.RemoveBlock
