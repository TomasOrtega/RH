import Mathlib

open scoped BigOperators
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ U hU hc hne ι _ f hf hnz`. Set `S : ι → Set E` to `fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ`. Establish `hopen : ∀ i, IsOpen (S i)` using `fun i => ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union isClosed_closure.isOpen_compl`. Establish `hdense : ∀ i, Dense (S i)`. Introduce `i`.

Rewrite using `[dense_iff_inter_open]`. Introduce `V hV hVne`. Distinguish the cases in `hVU : (V ∩ U).Nonempty`. Take `⟨z, hzV, hzU⟩` from `hVU`. Assume the negation of the conclusion as `hcon`.

Establish `hzero : ∀ y ∈ V ∩ U, f i y = 0`. Introduce `y hy`. Assume the negation of the conclusion as `hy0`. Conclude with `hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩`. Establish `hev : f i =ᶠ[nhds z] 0` using `by filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy`.

Conclude with `hzero y hy`. Establish `hall` using `(hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev`. Take `⟨x, hxU, hx⟩` from `hnz i`. Conclude with `hx (hall hxU)`. Take `⟨z, hzV⟩` from `hVne`.

Use `⟨z, hzV, Or.inr ?_⟩` and prove the remaining obligations. Introduce `hz`. Conclude with `hVU (mem_closure_iff.1 hz V hV hzV)`. Establish `hD : Dense (⋂ i, S i)` using `dense_iInter_of_isOpen hopen hdense`. Take `⟨x, hxU, hx⟩` from `hD.inter_open_nonempty U hU hne`.

Use `⟨x, hxU, fun i => ?_⟩` and prove the remaining obligations. Break down `Set.mem_iInter.1 hx i with h | h` into its components or cases. Conclude with `h.2`. Conclude with `absurd (subset_closure hxU) h`.
-/
theorem exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by
  intro E _ _ _ U hU hc hne ι _ f hf hnz
  let S : ι → Set E := fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ
  have hopen : ∀ i, IsOpen (S i) := fun i =>
    ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (S i) := by
    intro i
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hVU : (V ∩ U).Nonempty
    · obtain ⟨z, hzV, hzU⟩ := hVU
      by_contra hcon
      have hzero : ∀ y ∈ V ∩ U, f i y = 0 := by
        intro y hy
        by_contra hy0
        exact hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩
      have hev : f i =ᶠ[nhds z] 0 := by
        filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy
        exact hzero y hy
      have hall := (hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev
      obtain ⟨x, hxU, hx⟩ := hnz i
      exact hx (hall hxU)
    · obtain ⟨z, hzV⟩ := hVne
      refine ⟨z, hzV, Or.inr ?_⟩
      intro hz
      exact hVU (mem_closure_iff.1 hz V hV hzV)
  have hD : Dense (⋂ i, S i) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := hD.inter_open_nonempty U hU hne
  refine ⟨x, hxU, fun i => ?_⟩
  rcases Set.mem_iInter.1 hx i with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory
