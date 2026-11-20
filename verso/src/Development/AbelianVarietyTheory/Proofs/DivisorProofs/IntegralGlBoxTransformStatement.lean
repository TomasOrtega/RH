import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGlBoxTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoxMove.boxmove` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralGlBoxTransform.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.integral_gl_box_transform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ϖ : kˣ) (g : GL (Fin n) k) (h : GL (Fin d) k), (∀ i j, valuation k (g.1 i j) ≤ 1) → (∀ i j, valuation k ((g⁻¹).1 i j) ≤ 1) → (∀ i j, valuation k (h.1 i j) ≤ 1) → (∀ i j, valuation k ((h⁻¹).1 i j) ≤ 1) → ∀ (C : Matrix (Fin n) (Fin d) k) (N : ℕ), {Y : Matrix (Fin n) (Fin d) k | (g.1)ᵀ * Y * h.1 ∈ box ϖ ((g.1)ᵀ * C * h.1) (fun _ => N)} = box ϖ C (fun _ => N) := by
  first | exact @GlobalTheory.BoxMove.boxmove | exact GlobalTheory.BoxMove.boxmove | (intros; apply GlobalTheory.BoxMove.boxmove <;> assumption)
