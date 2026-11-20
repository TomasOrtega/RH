import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUnitaryImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem unitarizable_of_separating_smooth_l2_maps : CompanionTheory.RgExh.Fin.UnitarizableOfL2Embedding := by
  intro n ε X hL hS
  obtain ⟨hnt, hsub⟩ := hS
  obtain ⟨u, hu⟩ := exists_ne (0 : X.V)
  obtain ⟨c, hc, hcu⟩ := hL u hu
  have h0 : c ≠ 0 := fun h => hcu (by simp [h])
  obtain ⟨V, E', e, -, hgl, hU, he⟩ :=
    GlobalTheory.CompanionTheory.Unitarize.exists_unitary_image (rreg_isURepOn ε) hsub c hc h0
  exact ⟨V, inferInstance, inferInstance, E', hgl, hU, e, he⟩

end GlobalTheory.CompanionTheory.RgExhFin
