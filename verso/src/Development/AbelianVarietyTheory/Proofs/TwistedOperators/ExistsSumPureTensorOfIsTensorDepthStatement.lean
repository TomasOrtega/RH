import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TensorExpansion.exists_sum_pureTensor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsSumPureTensorOfIsTensorDepth.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  first | exact @GlobalTheory.TensorExpansion.exists_sum_pureTensor | exact GlobalTheory.TensorExpansion.exists_sum_pureTensor | (intros; apply GlobalTheory.TensorExpansion.exists_sum_pureTensor <;> assumption)
