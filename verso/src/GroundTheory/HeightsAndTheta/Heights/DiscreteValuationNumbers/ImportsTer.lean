import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim`. Distinguish the cases in `hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U`. Use `swap`. Establish `hl` using `h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs`. Establish `hr` using `h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH`.

Unfold `cycEval`. Rewrite using `[finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]`. Take `⟨hUp, hUm, hUr, hϖU, hPU⟩` from `hU`. Establish `hUdim'` using `hUdim hUp hUm hUr hϖU`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`.

Establish `hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W` using `fun W hW k =>`. Set `⟨i, hi⟩` to `hUr k`. Use the proof step `⟨i, fun h => hi (hW h)⟩`. Establish `hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W`. Introduce `J W hW`.

Unfold `idealCycle locCycle`. Distinguish the cases in `hm : W ∈ J.minimalPrimes`. Rewrite using `[dif_pos ⟨hm, hW⟩, dif_pos hm]`. Both sides reduce to the same expression. Rewrite using `[dif_neg fun h => hm h.1, dif_neg hm]`.

Establish `hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0`. Introduce `J hJ`. Unfold `locCycle`. Rewrite using `[dif_neg fun h => hJ h.1.2]`. Establish `hL : ∀ G, ratDiv P f g G * divCycle G s U = (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) * locCycle (G ⊔ Ideal.span {s}) U`.

Introduce `G`. Rewrite using `[divCycle_eq_idealCycle, hcyc _ _ hUr]`. Distinguish the cases in `hG : G ≤ U`. Unfold `ratDiv`. Rewrite using `[divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]`.

Rewrite using `[hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]`. Establish `hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U = locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U`. Introduce `W`. Use `show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _`. Rewrite using `[hcyc _ _ hUr]`.

Distinguish the cases in `hW : W ≤ U`. Rewrite using `[divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]`. Rewrite using `[hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]`. Establish `hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False`. Introduce `Q₁ Q₂ _ _ hPQ hQQ hQU`.

Establish `e₁` using `DimStrictDrop.proof (MRing ι O) P Q₁ hPQ`. Establish `e₂` using `DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ`. Establish `e₃` using `DimStrictDrop.proof (MRing ι O) Q₂ U hQU`. Rewrite `e₁` using `[hP.dim]`. Establish `key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)` using `((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))`.

Establish `key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Simplify `key` using `only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three]`. Use `WithBot.coe_le_coe.mp key'` as an intermediate fact. Normalize the coercions in `at this`. Use linear arithmetic over natural numbers and integers.

Take `⟨u', v', hu', huv⟩` from `hD.2 U hUp hPU hUr`. Establish `hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 → locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W`. Introduce `W hW h`. Establish `hs' : divCycle P s W ≠ 0` using `by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]`. Establish `hr : ratDiv P f g W = 0`.

Distinguish the cases in `hϖW : (C ϖ : MRing ι O) ∈ W`. Conclude with `hno W hϖW hs'`. Assume the negation of the conclusion as `h`. Conclude with `hϖW (hD.1.vertical W h)`. Unfold `ratDiv at hr`.

Rewrite `hr` using `[divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW), hcyc _ _ (hrel W hW)]`. Use linear arithmetic over natural numbers and integers. Unfold `cycEval`. Rewrite using `[finsum_congr hL, finsum_congr hR]`. Conclude with `h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu' huv hnc`.
-/
theorem LocalCoefficient.proof (h₁ : LeftTermSupport.Statement.{u})
    (h₂ : RightTermSupport.Statement.{u}) (h₃ : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U
  swap
  ·
    have hl := h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs
    have hr := h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH
    unfold cycEval
    rw [finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]
  obtain ⟨hUp, hUm, hUr, hϖU, hPU⟩ := hU
  have hUdim' := hUdim hUp hUm hUr hϖU
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W := fun W hW k =>
    let ⟨i, hi⟩ := hUr k
    ⟨i, fun h => hi (hW h)⟩
  have hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W := by
    intro J W hW
    unfold idealCycle locCycle
    by_cases hm : W ∈ J.minimalPrimes
    · rw [dif_pos ⟨hm, hW⟩, dif_pos hm]
      rfl
    · rw [dif_neg fun h => hm h.1, dif_neg hm]
  have hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0 := by
    intro J hJ
    unfold locCycle
    rw [dif_neg fun h => hJ h.1.2]
  have hL : ∀ G, ratDiv P f g G * divCycle G s U =
      (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U := by
    intro G
    rw [divCycle_eq_idealCycle, hcyc _ _ hUr]
    by_cases hG : G ≤ U
    · unfold ratDiv
      rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]
    · rw [hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]
  have hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U =
      locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U := by
    intro W
    show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _
    rw [hcyc _ _ hUr]
    by_cases hW : W ≤ U
    · rw [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    · rw [hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]

  have hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U →
      False := by
    intro Q₁ Q₂ _ _ hPQ hQQ hQU
    have e₁ := DimStrictDrop.proof (MRing ι O) P Q₁ hPQ
    have e₂ := DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ
    have e₃ := DimStrictDrop.proof (MRing ι O) Q₂ U hQU
    rw [hP.dim] at e₁
    have key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤
        ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      ((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans
        ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))
    have key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three] using key
    have := WithBot.coe_le_coe.mp key'
    norm_cast at this
    omega

  obtain ⟨u', v', hu', huv⟩ := hD.2 U hUp hPU hUr

  have hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W := by
    intro W hW h
    have hs' : divCycle P s W ≠ 0 := by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    have hr : ratDiv P f g W = 0 := by
      by_cases hϖW : (C ϖ : MRing ι O) ∈ W
      · exact hno W hϖW hs'
      · by_contra h
        exact hϖW (hD.1.vertical W h)
    unfold ratDiv at hr
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW),
      hcyc _ _ (hrel W hW)] at hr
    omega
  unfold cycEval
  rw [finsum_congr hL, finsum_congr hR]
  exact h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu'
    huv hnc

end GroundTheory.Heights₂.Heights.NumbersDVR
