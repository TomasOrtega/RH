import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLawsB

namespace CrystallineSemistableComparison.Onto

/- English proof (translation)
Introduce `K _ W Z Y q i _ π d V c`. Take `⟨h1, h2, h3⟩` from `chartLaws_A K W Z Y q i π d V c`. Conclude with `⟨h1, h2, h3, fun k D h hD => chartLaws_B K W Z Y q i π d V c k D h hD⟩`.
-/
theorem chartLaws_pf : ChartLaws := by
  intro K _ W Z Y q i _ π d V c
  obtain ⟨h1, h2, h3⟩ := chartLaws_A K W Z Y q i π d V c
  exact ⟨h1, h2, h3, fun k D h hD => chartLaws_B K W Z Y q i π d V c k D h hD⟩

end CrystallineSemistableComparison.Onto
