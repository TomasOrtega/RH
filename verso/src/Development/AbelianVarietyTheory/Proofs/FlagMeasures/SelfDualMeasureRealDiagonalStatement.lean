import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSelfDualMeasureRealDiagonal.lean&line=167#L167)
-/
theorem _root_.GlobalTheory.T.self_dual_measure_real_diagonal : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) → ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) → μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  first | exact @GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | exact GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | (intros; apply GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag <;> assumption)
