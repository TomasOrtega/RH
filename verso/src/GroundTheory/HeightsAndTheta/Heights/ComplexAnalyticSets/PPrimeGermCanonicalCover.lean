import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermCanonicalCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermPrimitivePresentation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitivePresentationCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
