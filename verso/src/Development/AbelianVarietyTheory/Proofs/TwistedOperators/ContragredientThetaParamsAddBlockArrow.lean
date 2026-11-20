import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

/- English proof (translation)
Introduce `D hS i j τ hi hj`. Establish `hnear` using `grid_nearMid D τ`. Establish `hB1` using `gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ`. Establish `hbe` using `grid_hbe D τ`. Establish `heb` using `grid_heb D τ`.

Establish `hbb` using `grid_hbb D τ hS`. Establish `hga` using `grid_hga D τ`. Establish `hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3` using `by positivity`. Establish `hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga` using `by linarith`. Establish `hsOdd` using `odd_sLen D`.

Establish `hle` using `entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2`. Establish `hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3)` using `fun i' => gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga`. Establish `hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ)` using `fun x hx => hle x.1 (fst_mem_entries hx)`. Establish `hs0 : (0 : ℚ) ≤ sLen D` using `by positivity`. Use `set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc`.

Use `set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef`. Use `set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def`. Establish `e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j)`. Rewrite using `[show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one`. Establish `hδ : att c (rkV D (i + 1) j) = c + δ`.

Distinguish the cases in `h : Odd (i + j)`. Simplify using `[att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]`. Simplify using `[att, odd_rkV_iff, e1, h, hδdef]`. Establish `hδ' : att c (rkV D i j) = c + δ'`. Distinguish the cases in `h : Odd (i + j)`.

Simplify using `[att, odd_rkV_iff, e1, h, hδ'def]`. Simplify using `[att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]`. Establish `key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) = flip (shift δ' ((grid D τ).parD (i + 1) j))`. Rewrite using `[parD_succ _ hi]`. Use extensionality with `y`.

Simplify using `only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)`. Use `hlt _ hx left` as an intermediate fact. Rewrite using `[if_pos (by simp only at this; linarith)]`.

Simplify using `only [Bool.not_not]`. Use `hx using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `right`. Use `⟨?_, rfl⟩` and prove the remaining obligations.

Use `show z - δ' ∈ TPar.block c (sLen D)`. Conclude with `sub_mem_block.2 (by simpa [add_comm] using hz)`. Introduce and unpack `(h | ⟨h1, h2⟩)`. Use `left`. Use `⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩` and prove the remaining obligations.

Use `hlt _ h` as an intermediate fact. Rewrite using `[if_pos (by simp only at this ⊢; linarith)]`. Use `ext`. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Use `right`. Use `⟨y.1, ?_, ?_⟩` and prove the remaining obligations. Establish `: y.1 - δ' ∈ TPar.block c (sLen D)` using `h1`. Simplify `sub_mem_block.1 this` using `[add_comm]`.

Use `ext`. Both sides reduce to the same expression. Simplify using `using h2`. Use `⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩` and prove the remaining obligations. Conclude with `flip_dualPar _`.

Rewrite using `[hδ, hδ', ← key]`. Establish `hX : ((grid D τ).parD i j).Nonempty` using `⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩`. Establish `hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2)`. Introduce `a b e`. Simplify using `only [Prod.mk.injEq, add_left_inj] at e`.

Conclude with `Prod.ext e.1 e.2`. Establish `hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D`. Rewrite using `[shift, card_image_of_injective _ hinj]`. Establish `h1` using `card_parD_le (grid D τ) (i := i) (j := j) hi.le`. Establish `h2 : j * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ hj`.

Establish `h3 : (i + 1) * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ hi`. Establish `hr : D.R.r + 1 = D.R.k + D.R.m` using `by have := D.R.m_add_three_le_k; unfold Ranks.r; omega`. Express the relevant statement in the definitionally equal form `_ ≤ D.R.r + j * D.R.t + i * sLen D at h1`. Unfold `bigN`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hN : 1800 < bigN D`. Use `hS.1` as an intermediate fact. Establish `hr : D.R.r + 1 = D.R.k + D.R.m` using `by have := D.R.m_add_three_le_k; unfold Ranks.r; omega`. Unfold `bigN`. Use the polynomial consequences of the given equalities and inequalities.

Use `GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _) (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i)) (by rw [key]; exact gapOver_flip (gapOv …` and prove the remaining obligations. Introduce `x hx`. Take `⟨sg, hsg⟩` from `mem_entries.1 hx`. Establish `h` using `mem_shift.1 hsg`. Take `⟨z, hz⟩` from `int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)`.

Take `⟨w, hw⟩` from `hsOdd`. Simplify using `only at hz`. Use `⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx`. Take `⟨sg, hsg⟩` from `mem_entries.1 hx`. Establish `h` using `hlt _ (mem_shift.1 hsg)`. Simplify using `only at h`.

Rewrite using `[abs_sub_comm, abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pairPar_X : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m →
    PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j))
      (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  intro D hS i j τ hi hj
  have hnear := grid_nearMid D τ
  have hB1 := gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ
  have hbe := grid_hbe D τ
  have heb := grid_heb D τ
  have hbb := grid_hbb D τ hS
  have hga := grid_hga D τ
  have hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga := by linarith
  have hsOdd := odd_sLen D
  have hle := entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2
  have hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3) := fun i' =>
    gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga
  have hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ) := fun x hx =>
    hle x.1 (fst_mem_entries hx)
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def
  have e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one
  have hδ : att c (rkV D (i + 1) j) = c + δ := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]
    · simp [att, odd_rkV_iff, e1, h, hδdef]
  have hδ' : att c (rkV D i j) = c + δ' := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδ'def]
    · simp [att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]
  have key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) =
      flip (shift δ' ((grid D τ).parD (i + 1) j)) := by
    rw [parD_succ _ hi]
    ext y
    simp only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
      · have := hlt _ hx
        left
        rw [if_pos (by simp only at this; linarith)]
        simp only [Bool.not_not]
        convert hx using 2
        ring
      · right
        refine ⟨?_, rfl⟩
        show z - δ' ∈ TPar.block c (sLen D)
        exact sub_mem_block.2 (by simpa [add_comm] using hz)
    · rintro (h | ⟨h1, h2⟩)
      · left
        refine ⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩
        have := hlt _ h
        rw [if_pos (by simp only at this ⊢; linarith)]
        ext
        · simp only; ring
        · simp
      · right
        refine ⟨y.1, ?_, ?_⟩
        · have : y.1 - δ' ∈ TPar.block c (sLen D) := h1
          simpa [add_comm] using sub_mem_block.1 this
        · ext
          · rfl
          · simpa using h2
  refine ⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩
  · exact flip_dualPar _
  · rw [hδ, hδ', ← key]
    have hX : ((grid D τ).parD i j).Nonempty :=
      ⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩
    have hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2) := by
      intro a b e
      simp only [Prod.mk.injEq, add_left_inj] at e
      exact Prod.ext e.1 e.2
    have hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D := by
      rw [shift, card_image_of_injective _ hinj]
      have h1 := card_parD_le (grid D τ) (i := i) (j := j) hi.le
      have h2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have h3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      change _ ≤ D.R.r + j * D.R.t + i * sLen D at h1
      unfold bigN
      nlinarith
    have hN : 1800 < bigN D := by
      have := hS.1
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      unfold bigN
      nlinarith
    refine GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _)
      (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i))
      (by rw [key]; exact gapOver_flip (gapOver_shift δ' (hgap (i + 1))))
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := mem_shift.1 hsg
      obtain ⟨z, hz⟩ := int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)
      obtain ⟨w, hw⟩ := hsOdd
      simp only at hz
      refine ⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩
      rw [hw]
      push_cast
      linarith
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := hlt _ (mem_shift.1 hsg)
      simp only at h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith

end GlobalTheory.GridParD

end
