import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjective
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEvalQuotientRingVectorAtPointsInjective.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.evalQuotientRingVectorAtPoints_injective : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ), Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  first | exact @GlobalTheory.HerbrandBridge.evalVec_injective_of_injective | exact GlobalTheory.HerbrandBridge.evalVec_injective_of_injective | (intros; apply GlobalTheory.HerbrandBridge.evalVec_injective_of_injective <;> assumption)
