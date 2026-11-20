import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilThetaConvergenceOfSiegelSet
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds

namespace UpperTheory.Lit

/- English proof (translation)
The claim follows from `PositivityTheory.ThKR.siegel_of_core PositivityTheory.Prw.siegelCore_holds`.
-/
theorem siegelSetUnitary_of_core : GlobalTheory.Published.SiegelSetUnitary := PositivityTheory.ThKR.siegel_of_core PositivityTheory.Prw.siegelCore_holds

/- English proof (translation)
The claim follows from `GlobalTheory.WeilThetaConv.weilThetaConvergence_of_siegelSet siegelSetUnitary_of_core`.
-/
theorem weilThetaConvergence : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.WeilThetaConv.weilThetaConvergence_of_siegelSet siegelSetUnitary_of_core

end UpperTheory.Lit
