import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce `R _ n z hz x w hx hw`. Take `⟨h1, h2, h3⟩` from `hz`. Take `⟨f, hf⟩` from `List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx`. Take `⟨g, hg⟩` from `List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hw`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[hf i, hf j, h1 (f i) (f j)]`. Simplify using `only [f.eq_iff_eq]`. Take `⟨F, hF⟩` from `h2`. Use `⟨fun i => F (g i), fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hg j, hF]`. Simplify using `only [g.eq_iff_eq]`. Introduce `y hy u hu`. Conclude with `h3 y (hx.subset hy) u (hw.subset hu)`.
-/
theorem splitPairs_subClosed2 : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  intro R _ n z hz x w hx hw
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hw
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hf i, hf j, h1 (f i) (f j)]
    simp only [f.eq_iff_eq]
  · obtain ⟨F, hF⟩ := h2
    refine ⟨fun i => F (g i), fun i j => ?_⟩
    rw [hg j, hF]
    simp only [g.eq_iff_eq]
  · intro y hy u hu
    exact h3 y (hx.subset hy) u (hw.subset hu)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.splitPairs_subClosed2`.
-/
theorem _root_.GlobalTheory.T.subClosed2_splitPairs : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  first
  | exact @GlobalTheory.SeqCx.splitPairs_subClosed2
end
