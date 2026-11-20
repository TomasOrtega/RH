import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnfoldingIntegralEqFiniteSumOverNumberField.lean&line=257#L257)
-/
theorem _root_.GlobalTheory.T.unfoldingIntegral_eq_finiteSum_overNumberField : SumAgree := by
  first | exact @GlobalTheory.UnfoldSum.sumAgree | exact GlobalTheory.UnfoldSum.sumAgree | (intros; apply GlobalTheory.UnfoldSum.sumAgree <;> assumption)
