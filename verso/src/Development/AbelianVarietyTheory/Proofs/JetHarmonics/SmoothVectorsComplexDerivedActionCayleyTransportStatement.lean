import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransport
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CayleyTransport.smooth_and_dsigC_transport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FSmoothVectorsComplexDerivedActionCayleyTransport.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  first | exact @GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | exact GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | (intros; apply GlobalTheory.CayleyTransport.smooth_and_dsigC_transport <;> assumption)
