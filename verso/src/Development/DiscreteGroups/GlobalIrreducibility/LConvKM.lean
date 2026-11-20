import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvKMCore

namespace DiscreteGroups.sglob.LConv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
