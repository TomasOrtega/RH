import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullbackStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.isForm_del_dbar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolAtlasIsFormDelDbarSmooth.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.holAtlas_isForm_del_dbar_smooth : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.isForm_del_dbar | exact GlobalTheory.CxForm.isForm_del_dbar | (intros; apply GlobalTheory.CxForm.isForm_del_dbar <;> assumption)
