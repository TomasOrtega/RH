import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FInvariantExtensionIntegrableOnCompact.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.invariantExtension_integrableOn_compact : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ, ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧ ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.LocalL2Isometry.ext_integrableOn | exact GlobalTheory.LocalL2Isometry.ext_integrableOn | (intros; apply GlobalTheory.LocalL2Isometry.ext_integrableOn <;> assumption)
