import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

/- English proof (translation)
Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Set `e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `a : Fin (finrank ℚ E) → 𝓞 E` to `fun i => RingOfIntegers.basis E (e i)`. Use `⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩` and prove the remaining obligations.

Use `(integralBasis E).linearIndependent.comp e e.injective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[a, integralBasis_apply]`. Introduce `i σ`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
