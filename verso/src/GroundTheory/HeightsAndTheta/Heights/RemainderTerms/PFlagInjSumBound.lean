import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on_max with`. Consider the case `empty => simp`. Consider the case `insert m S' hlt ih`. Take `⟨ih₁, ih₂⟩` from `ih`. Establish `hm : m ∉ S'` using `fun h => lt_irrefl m (hlt m h)`.

Establish `hsub : S' ⊆ Finset.range m` using `fun x hx => Finset.mem_range.2 (hlt x hx)`. Establish `hcard : S'.card ≤ m` using `by simpa using Finset.card_le_card hsub`. Rewrite using `[Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]`. Use `⟨by omega, fun heq => ?_⟩` and prove the remaining obligations. Establish `hmeq : m = S'.card` using `by omega`.

Establish `hS'` using `ih₂ (by omega)`. Introduce `x hx`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `Finset.mem_range.2 (by omega)`. Conclude with `Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))`.
-/
theorem FlagInjSumBound.finset_sum_bound (S : Finset ℕ) :
    ∑ i ∈ Finset.range S.card, i ≤ ∑ x ∈ S, x ∧
      (∑ x ∈ S, x = ∑ i ∈ Finset.range S.card, i → S ⊆ Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert m S' hlt ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hm : m ∉ S' := fun h => lt_irrefl m (hlt m h)
    have hsub : S' ⊆ Finset.range m := fun x hx => Finset.mem_range.2 (hlt x hx)
    have hcard : S'.card ≤ m := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hm, Finset.sum_range_succ, Finset.sum_insert hm]
    refine ⟨by omega, fun heq => ?_⟩
    have hmeq : m = S'.card := by omega
    have hS' := ih₂ (by omega)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_range.2 (by omega)
    · exact Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hS' hx)))

/- English proof (translation)
Introduce `N g hg`. Use `set S := Finset.univ.image g with hSdef`. Establish `hcard : S.card = N`. Rewrite using `[hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]`. Establish `hsum : ∑ i, g i = ∑ x ∈ S, x`.

Rewrite using `[hSdef, Finset.sum_image (fun i _ j _ h => hg h)]`. Take `⟨h₁, h₂⟩` from `FlagInjSumBound.finset_sum_bound S`. Rewrite `h₁`, `h₂` using `[hcard, Finset.sum_range_id]`. Rewrite using `[hsum]`. Use `⟨h₁, fun heq i => ?_⟩` and prove the remaining obligations.

Establish `hi : g i ∈ S` using `Finset.mem_image_of_mem g (Finset.mem_univ i)`. Conclude with `Finset.mem_range.1 (h₂ heq hi)`.
-/
theorem FlagInjSumBound.proof : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)

end RestTerms

end GroundTheory.Heights₂.Heights
