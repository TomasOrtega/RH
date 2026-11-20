import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsB

namespace CrystallineSemistableComparison.Onto

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem chartLaws_pf : ChartLaws := by
  intro K _ W Z Y q i _ π d V c
  obtain ⟨h1, h2, h3⟩ := chartLaws_A K W Z Y q i π d V c
  exact ⟨h1, h2, h3, fun k D h hD => chartLaws_B K W Z Y q i π d V c k D h hD⟩

end CrystallineSemistableComparison.Onto
