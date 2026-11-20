import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmType
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodicBoundedGaussianSummableCmType.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.periodic_bounded_gaussian_summable_cmType : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧ (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K => ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧ ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  first | exact @GlobalTheory.HeckeLat.periodic_bound_summable_norm | exact GlobalTheory.HeckeLat.periodic_bound_summable_norm | (intros; apply GlobalTheory.HeckeLat.periodic_bound_summable_norm <;> assumption)
