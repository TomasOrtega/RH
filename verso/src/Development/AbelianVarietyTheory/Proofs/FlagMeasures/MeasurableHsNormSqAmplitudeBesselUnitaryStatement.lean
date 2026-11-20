import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMeasurableHsNormSqAmplitudeBesselUnitary.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  first | exact @GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | exact GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | (intros; apply GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ <;> assumption)
