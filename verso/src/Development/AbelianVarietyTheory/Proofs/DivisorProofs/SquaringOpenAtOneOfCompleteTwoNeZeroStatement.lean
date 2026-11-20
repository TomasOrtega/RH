import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSquaringOpenAtOneOfCompleteTwoNeZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  first | exact @GlobalTheory.sqOpen_of_two_ne_zero | exact GlobalTheory.sqOpen_of_two_ne_zero | (intros; apply GlobalTheory.sqOpen_of_two_ne_zero <;> assumption)
