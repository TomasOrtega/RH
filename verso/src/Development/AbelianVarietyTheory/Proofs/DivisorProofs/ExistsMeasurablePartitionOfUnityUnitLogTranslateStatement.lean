import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMeasurablePartitionOfUnityUnitLogTranslate.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  first | exact @GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | exact GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | (intros; apply GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates <;> assumption)
