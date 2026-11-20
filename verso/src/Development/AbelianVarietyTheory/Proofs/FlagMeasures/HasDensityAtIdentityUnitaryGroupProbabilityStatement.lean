import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryVolume.hasDens_unitary` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHasDensityAtIdentityUnitaryGroupProbability.lean&line=243#L243)
-/
theorem _root_.GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability : ∀ (j : ℕ) (μ : Measure (PI.MtM j)), PI.IsHaarOnM (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ → μ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ (ENNReal.ofReal (volUn j)⁻¹) := by
  first | exact @GlobalTheory.UnitaryVolume.hasDens_unitary | exact GlobalTheory.UnitaryVolume.hasDens_unitary | (intros; apply GlobalTheory.UnitaryVolume.hasDens_unitary <;> assumption)
