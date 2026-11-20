import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.stripLow_integrableOn_im_rpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIntegrableOnImRpowUnitStripBelowOne.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
