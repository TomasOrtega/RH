import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRootMeasureEqNormalFormRootMeasure.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  first | exact @GlobalTheory.Amp.RootNormal.rootMeas_normR | exact GlobalTheory.Amp.RootNormal.rootMeas_normR | (intros; apply GlobalTheory.Amp.RootNormal.rootMeas_normR <;> assumption)
