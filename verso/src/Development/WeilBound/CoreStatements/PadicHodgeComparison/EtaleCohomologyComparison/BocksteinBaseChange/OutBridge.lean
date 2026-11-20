import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CstSmooth
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

noncomputable section

namespace CrystallineSemistableComparison.Out

/- English proof (translation)
The claim follows from `CrystallineSemistableComparison.cstSmooth_of_side h`.
-/
theorem cstSmooth_of_side (h : EtSideS) : CstSmooth := CrystallineSemistableComparison.cstSmooth_of_side h

end CrystallineSemistableComparison.Out
