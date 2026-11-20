import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Equiv

/- English proof (translation)
Introduce `m l hl q hq i j hij hqi hqj σ τ heq`. Establish `hr` using `congrArg Set.range heq`. Rewrite `hr` using `[σ.surjective.range_comp, τ.surjective.range_comp]`. Establish `hmem : l i ∈ Set.range (Function.update l j (l j - q))` using `⟨i, by rw [Function.update_of_ne hij]⟩`. Rewrite `hmem` using `[← hr]`.

Take `⟨k, hk⟩` from `hmem`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Rewrite `hk` using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hk` using `[Function.update_of_ne hki]`. Conclude with `hki (hl hk)`.
-/
theorem CombSortShiftDistinct.proof : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)

end GroundTheory.Heights₂.Heights.RestTerms
