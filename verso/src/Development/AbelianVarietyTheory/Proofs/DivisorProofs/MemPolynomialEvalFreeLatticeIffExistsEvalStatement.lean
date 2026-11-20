import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEval
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EvalVecRange.evalVec_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemPolynomialEvalFreeLatticeIffExistsEval.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.mem_polynomialEvalFreeLattice_iff_exists_eval : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y := by
  first | exact @GlobalTheory.EvalVecRange.evalVec_range | exact GlobalTheory.EvalVecRange.evalVec_range | (intros; apply GlobalTheory.EvalVecRange.evalVec_range <;> assumption)
