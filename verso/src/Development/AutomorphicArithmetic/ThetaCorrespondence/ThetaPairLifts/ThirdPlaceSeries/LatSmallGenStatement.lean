import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FLatSmallGenAltAlt.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.latSmallGen' : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | exact _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt <;> assumption)
end
