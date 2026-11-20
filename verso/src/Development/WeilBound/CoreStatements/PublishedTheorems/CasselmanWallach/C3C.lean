import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `n ε V _ _ E hgl hun S hfd hS hne`. Take `⟨w, hw, hw0, μ, hμ⟩` from `ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne`. Conclude with `⟨w, μ, hw, hw0, hμ⟩`.
-/
theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
