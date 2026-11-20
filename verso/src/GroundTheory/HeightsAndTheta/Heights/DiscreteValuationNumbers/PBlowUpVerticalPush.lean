import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpVerticalFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

open Classical in
/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a`. Establish `hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J` using `J) x))).Finite := DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _`. Establish `hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔ (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι` using `ι) (J := J) (R := O)) := by`. Introduce `W'`. Rewrite using `[Ideal.mem_comap]`.

Simplify using `[liftForm]`. Use `set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' => divCycle (blowUpOf P u) (liftForm x) W' * (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def`. Establish `hg : Function.support g ⊆ hZ.toFinset` using `fun W' hW' => hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')`. Establish `key : ∀ W : Ideal (MRing ι O), (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι` using `ι) (J := J) (R := O)) = W, g W') = divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by`. Introduce `W`.

Distinguish the cases in `hW : (C ϖ : MRing ι O) ∈ W`. Rewrite using `[if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW, finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]`. Use `Finset.sum_congr rfl fun W' _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W`. Rewrite using `[if_pos h1, if_pos h1, hg_def] dsimp only`.

Rewrite using `[if_pos ((hC W').mpr (by rw [h1]; exact hW))]`. Rewrite using `[if_neg h1, if_neg h1]`. Introduce `W' hW'`. Use `hZ.mem_toFinset.mpr ?_` and prove the remaining obligations. Rewrite `hW'`, the goal using `[Function.mem_support]`.

Introduce `h0`. Apply `hW'` to reduce the goal to its premises. Simplify using `[h0]`. Rewrite using `[if_neg hW, mul_zero]`. Use `Finset.sum_eq_zero fun W' hW' => ?_` and prove the remaining obligations.

Establish `h1` using `(Finset.mem_filter.mp hW').2`. Rewrite using `[hg_def]`. Simplify using `only`. Rewrite using `[if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]`. Unfold `cycEval`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem BlowUpVerticalPush.proof (hfib : BlowUpVerticalFibre.Statement.{u}) :
    BlowUpVerticalPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a
  have hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J := J) x))).Finite :=
    DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _

  have hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔
      (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    intro W'
    rw [Ideal.mem_comap]
    simp [liftForm]
  set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' =>
    divCycle (blowUpOf P u) (liftForm x) W' *
      (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')

  have key : ∀ W : Ideal (MRing ι O),
      (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W') =
        divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by
    intro W
    by_cases hW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((hC W').mpr (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]
  unfold cycEval
  calc (∑ᶠ W', divCycle (blowUpOf P u) (liftForm x) W' *
          (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0))
      = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end GroundTheory.Heights₂.Heights.NumbersDVR
