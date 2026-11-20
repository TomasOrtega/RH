import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRankStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCount

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ResidualRankCount.residual_count_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FResidualCount.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  first | exact @_root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | exact _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | (intros; apply _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt <;> assumption)
end
