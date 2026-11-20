import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentral
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Alc.glRel_pow_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FGlMatrixUnitPowCommutatorAndTraceCentral.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first | exact @GlobalTheory.Alc.glRel_pow_comm | exact GlobalTheory.Alc.glRel_pow_comm | (intros; apply GlobalTheory.Alc.glRel_pow_comm <;> assumption)
