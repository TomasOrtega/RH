import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrameCoeffRingPrimeNotIsUnit.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.frameCoeffRing_prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  first | exact @GlobalTheory.ExpFrame.Frame.prime_not_isUnit | exact GlobalTheory.ExpFrame.Frame.prime_not_isUnit | (intros; apply GlobalTheory.ExpFrame.Frame.prime_not_isUnit <;> assumption)
