import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermCanonicalCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitivePresentationCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Introduce `σ _ w k p hp hP`. Take `⟨d, A, ℓ, N, c, δ, hpres, hδ⟩` from `h₁ σ w k p hp hP`. Establish `hδa : AnalyticAt ℂ δ (A w)` using `hpres.2.1`. Establish `hdiv` using `hpres.2.2.2.2.2.1`. Use `⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩` and prove the remaining obligations.

Introduce `g hg`. Take `⟨M, a, ha, h, hh, hev⟩` from `hdiv g hg`. Conclude with `⟨M, a, h, ha, hh, hev⟩`.
-/
theorem PrimeGermCanonicalCover.proof (h₁ : PrimeGermPrimitivePresentation.Statement)
    (h₂ : PrimitivePresentationCover.Statement) : PrimeGermCanonicalCover.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, ℓ, N, c, δ, hpres, hδ⟩ := h₁ σ w k p hp hP
  have hδa : AnalyticAt ℂ δ (A w) := hpres.2.1
  have hdiv := hpres.2.2.2.2.2.1
  refine ⟨d, A, ℓ, N, δ, hδa, hδ, ?_, h₂ σ w k p d A ℓ N c δ hp hpres⟩
  intro g hg
  obtain ⟨M, a, ha, h, hh, hev⟩ := hdiv g hg
  exact ⟨M, a, h, ha, hh, hev⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
