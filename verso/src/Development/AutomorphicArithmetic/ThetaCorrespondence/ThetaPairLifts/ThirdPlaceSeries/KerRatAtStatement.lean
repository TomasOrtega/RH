import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStableStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerRatAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FKerRatAt.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.kernel_rationality_of_reciprocity_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt <;> assumption)
end
