import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass

namespace GlobalTheory.DiscreteSeriesConsequences

/- English proof (translation)
Introduce `h`. Take `⟨hE, -, hU, hI, hM, -, -⟩` from `GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)`. Conclude with `⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩`.
-/
theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
