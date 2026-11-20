import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDelDbarCommPullbackOfSmoothDelDbar.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | exact GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback <;> assumption)
