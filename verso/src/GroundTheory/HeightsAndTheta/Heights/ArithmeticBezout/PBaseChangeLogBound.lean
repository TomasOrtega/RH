import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

/- English proof (translation)
Introduce `K _ _ n e δ h I f u σ hI hf hδ hu`. Take `⟨hprime, c, hc, g, hg, heq⟩` from `hB K n (e + 1) I f σ hI hf`. Establish `hδσ : IsMultiHomog δ (MvPolynomial.map σ f)` using `(isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ`. Establish `hne : MvPolynomial.map σ f ≠ 0` using `fun h0 => hf.1 (map_injective σ σ.injective (by rw [h0, map_zero]))`. Rewrite `hδσ`, `hne` using `[heq]`.

Take `⟨δW, hδW, hsum⟩` from `exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδσ hne`. Unfold `cycleIntegral`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hsum]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BaseChangeLogBound.proof (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hC : ConeLogBound.Statement) : BaseChangeLogBound.Statement := by
  intro K _ _ n e δ h I f u σ hI hf hδ hu
  obtain ⟨hprime, c, hc, g, hg, heq⟩ := hB K n (e + 1) I f σ hI hf
  have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
    (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
  have hne : MvPolynomial.map σ f ≠ 0 := fun h0 =>
    hf.1 (map_injective σ σ.injective (by rw [h0, map_zero]))
  rw [heq] at hδσ hne
  obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) _ c g hg hδσ hne
  unfold cycleIntegral
  calc ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * coneIntegral h W e (fsLog h fun j => σ (u j))
      ≤ ∑ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support,
        ((fundCycle (I.map (MvPolynomial.map σ))) W : ℝ) * (δW W * Real.log (h.norm fun j => σ (u j))) :=
        Finset.sum_le_sum fun W hW => mul_le_mul_of_nonneg_left
          (hC n e (δW W) h W (g W) _ (hprime W hW) (hg W hW) (hδW W hW) (hAv K n I u σ hI hu W hW))
          (Nat.cast_nonneg _)
    _ = δ * Real.log (h.norm fun j => σ (u j)) := by
        rw [← hsum]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W _ => ?_
        ring

end

end GroundTheory.Heights₂.Heights
