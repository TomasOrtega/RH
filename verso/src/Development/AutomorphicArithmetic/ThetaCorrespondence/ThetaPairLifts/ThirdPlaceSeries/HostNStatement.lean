import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FHostN.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
