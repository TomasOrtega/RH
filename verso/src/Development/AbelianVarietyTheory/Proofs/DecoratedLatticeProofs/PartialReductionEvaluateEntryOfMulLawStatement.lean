import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEvaluateEntryOfMulLaw
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FPartialReductionEvaluateEntryOfMulLaw.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  first | exact @GlobalTheory.PartRedEval.kills_insert_of_evalLaw | exact GlobalTheory.PartRedEval.kills_insert_of_evalLaw | (intros; apply GlobalTheory.PartRedEval.kills_insert_of_evalLaw <;> assumption)
