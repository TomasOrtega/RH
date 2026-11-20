import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankCoinv.omA_diag_boxFn_succ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoxFunctionDiagonalAction.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.box_function_diagonal_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  first | exact @GlobalTheory.RankCoinv.omA_diag_boxFn_succ | exact GlobalTheory.RankCoinv.omA_diag_boxFn_succ | (intros; apply GlobalTheory.RankCoinv.omA_diag_boxFn_succ <;> assumption)
