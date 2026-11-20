import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws.
-/
theorem exactAt_of_links_cone : ∀ (V : Type) (F : Set (List V)) (S : Set V) (y : V), SubClosed F →
    (∀ l ∈ linkIn F S [], y :: l ∈ F) → ∀ (p : ℕ),
    (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
      ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S y hF hy p hlink c hc hbd
  obtain ⟨b, hb, hc', hbd'⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p hlink c hc hbd
  obtain ⟨b', hb', hbb'⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone V F (linkIn F S []) y hy p (c - bd V b) hc' hbd'
  refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
  rw [map_add, hbb']
  abel

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
end
