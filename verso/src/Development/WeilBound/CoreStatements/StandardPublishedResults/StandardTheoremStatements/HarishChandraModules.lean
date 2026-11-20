import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

namespace PositivityTheory.Stage1.PM

/- English proof (translation)
The claim follows from `CompanionTheory.D.gk.HC.print_harishChandraModules`.
-/
theorem harishChandraModules : GlobalTheory.Published.HarishChandraModules :=
  CompanionTheory.D.gk.HC.print_harishChandraModules

/- English proof (translation)
The claim follows from `PositivityTheory.GreenCharacters.greenCuspidal`.
-/
theorem greenCuspidal : GlobalTheory.Published.GreenCuspidal :=
  PositivityTheory.GreenCharacters.greenCuspidal

end PositivityTheory.Stage1.PM
