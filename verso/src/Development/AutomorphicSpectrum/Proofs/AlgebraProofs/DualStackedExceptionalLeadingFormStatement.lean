import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingForm
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDualStackedExceptionalLeadingForm.lean&line=326#L326)
-/
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_leading_form : GroundTheory.Heights₂.Heights.DualStackedExcLeadForm.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | exact GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm <;> assumption)
