import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `V F S hF p h c hc hcb`. Establish `hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q`. Introduce `q`. Apply `Finsupp.supported_mono` to reduce the goal to its premises. Introduce and unpack `l ⟨⟨_, hl⟩, hlen⟩`.

Conclude with `⟨by simpa using hl, hlen⟩`. Distinguish the cases in `h0 : ([] : List V) ∈ F`. Take `⟨b, hb, hcb', hcyc⟩` from `T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb`. Take `⟨b', hb', hbd⟩` from `h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc`. Use `⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hbd]`. Normalize the expressions using the abelian group laws. Establish `hFe : ∀ l, l ∉ F` using `fun l hl => h0 (hF l hl [] (List.nil_sublist l))`. Establish `hc0 : c = 0`. Establish `: {l : List V | l ∈ F ∧ l.length = p} = ∅`.

Use extensionality with `l`. Simplify using `[hFe l]`. Establish `hc'` using `hc`. Simplify using `only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'`. Conclude with `hc'`.

Conclude with `⟨0, Submodule.zero_mem _, by simp [hc0]⟩`.
-/
theorem SeqCx.exactAt_of_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
    (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S hF p h c hc hcb
  have hsubF : ∀ q, chains (linkIn F S []) q ≤ chains F q := by
    intro q
    apply Finsupp.supported_mono
    rintro l ⟨⟨_, hl⟩, hlen⟩
    exact ⟨by simpa using hl, hlen⟩
  by_cases h0 : ([] : List V) ∈ F
  · obtain ⟨b, hb, hcb', hcyc⟩ :=
      T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p (fun τ hτ _ _ _ hl => h τ hτ hl) c hc hcb
    obtain ⟨b', hb', hbd⟩ := h [] h0 (by simp) (c - bd V b) (by simpa using hcb') hcyc
    refine ⟨b + b', (chains F (p + 1)).add_mem hb (hsubF _ (by simpa using hb')), ?_⟩
    rw [map_add, hbd]
    abel
  · have hFe : ∀ l, l ∉ F := fun l hl => h0 (hF l hl [] (List.nil_sublist l))
    have hc0 : c = 0 := by
      have : {l : List V | l ∈ F ∧ l.length = p} = ∅ := by
        ext l
        simp [hFe l]
      have hc' := hc
      simp only [chains, this, Finsupp.supported_empty, Submodule.mem_bot] at hc'
      exact hc'
    exact ⟨0, Submodule.zero_mem _, by simp [hc0]⟩

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.exactAt_of_links`.
-/
theorem _root_.GlobalTheory.T.seqComplex_exactAt_of_all_links_exactAt : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_of_links
end
