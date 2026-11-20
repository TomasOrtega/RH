import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsUnimodularBesselModelUnitaryGroup.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isUnimodular_besselModelUnitaryGroup : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  first | exact @GlobalTheory.SgInf.isUnimod_GG | exact GlobalTheory.SgInf.isUnimod_GG | (intros; apply GlobalTheory.SgInf.isUnimod_GG <;> assumption)
