import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleRetractionOfLinkExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryCompBoundaryApply

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce `V F S hF p hex`. Establish `key : ∀ k : ℕ, ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `c hc _`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, sub_zero]`. Use `Finsupp.supported_mono ?_ hc` and prove the remaining obligations. Introduce and unpack `l ⟨⟨hl, hS⟩, hp⟩`.

Conclude with `⟨⟨by simpa using hS, by simpa using hl⟩, hp⟩`. Consider the case `succ k ih`. Introduce `c hc h0`. Take `⟨b, hb, hcb⟩` from `GlobalTheory.T.seqChain_cycle_retraction_of_link_exact V F S hF p k (fun τ hτ x hx hxS _ hle => hex τ hτ x hx hxS hle) c hc h0`. Take `⟨b', hb', hcb'⟩` from `ih (c - bd V b) hcb (by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero])`.

Use `⟨b + b', Submodule.add_mem _ hb hb', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← sub_sub]`. Conclude with `hcb'`. Introduce `c hc h0`. Establish `hc' : c ∈ chains {l ∈ F | ∀ y ∈ l.drop p, y ∈ S} p`.

Use `Finsupp.supported_mono ?_ hc` and prove the remaining obligations. Introduce and unpack `l ⟨hl, hp⟩`. Use `⟨⟨hl, ?_⟩, hp⟩` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[List.drop_eq_nil_of_le hp.le]`.

Simplify using `at hy`. Take `⟨b, hb, hcb⟩` from `key p c hc' h0`. Conclude with `⟨b, hb, hcb, by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero]⟩`.
-/
theorem exists_sub_bd_mem_chains_linkIn_nil :
    ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ),
      (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
        ExactAt (linkIn F S τ) (p - τ.length)) →
      ∀ c ∈ chains F p, bd V c = 0 →
        ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  intro V F S hF p hex
  have key : ∀ k : ℕ, ∀ c ∈ chains {l ∈ F | ∀ y ∈ l.drop k, y ∈ S} p, bd V c = 0 →
      ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p := by
    intro k
    induction k with
    | zero =>
      intro c hc _
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero, sub_zero]
      refine Finsupp.supported_mono ?_ hc
      rintro l ⟨⟨hl, hS⟩, hp⟩
      exact ⟨⟨by simpa using hS, by simpa using hl⟩, hp⟩
    | succ k ih =>
      intro c hc h0
      obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.seqChain_cycle_retraction_of_link_exact V F S hF p k
        (fun τ hτ x hx hxS _ hle => hex τ hτ x hx hxS hle) c hc h0
      obtain ⟨b', hb', hcb'⟩ := ih (c - bd V b) hcb
        (by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero])
      refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
      rw [map_add, ← sub_sub]
      exact hcb'
  intro c hc h0
  have hc' : c ∈ chains {l ∈ F | ∀ y ∈ l.drop p, y ∈ S} p := by
    refine Finsupp.supported_mono ?_ hc
    rintro l ⟨hl, hp⟩
    refine ⟨⟨hl, ?_⟩, hp⟩
    intro y hy
    rw [List.drop_eq_nil_of_le hp.le] at hy
    simp at hy
  obtain ⟨b, hb, hcb⟩ := key p c hc' h0
  exact ⟨b, hb, hcb, by rw [map_sub, h0, GlobalTheory.T.seqChain_boundary_comp_boundary_apply, sub_zero]⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.exists_sub_bd_mem_chains_linkIn_nil`.
-/
theorem _root_.GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links : ∀ (V : Type) (F : Set (List V)) (S : Set V), SubClosed F → ∀ (p : ℕ), (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p → ExactAt (linkIn F S τ) (p - τ.length)) → ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), c - bd V b ∈ chains (linkIn F S []) p ∧ bd V (c - bd V b) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.exists_sub_bd_mem_chains_linkIn_nil
end
