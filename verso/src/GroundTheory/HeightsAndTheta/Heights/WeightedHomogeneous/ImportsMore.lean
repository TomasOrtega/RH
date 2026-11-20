import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ChartFormsAlt.equiv :
    _root_.GroundTheory.Heights₂.Heights.ChartFormsAlt.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartFormsAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hA ι n P (toObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨g, hg⟩ := hd₀ d hd
    obtain ⟨G, hGd, -⟩ := (exists_chartForms_iff_isFormSystem D d g).2 hg
    exact ⟨G, hGd⟩
  · intro hB ι _ _ n P D
    obtain ⟨d₀, hd₀⟩ := hB ι n P (ofObjects D)
    refine ⟨d₀, fun d hd ↦ ?_⟩
    obtain ⟨G, hGd⟩ := hd₀ d hd
    exact ⟨G.g, (isFormSystem_iff_exists_chartForms D d G.g).2 ⟨G, hGd, rfl⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
