import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.BettiB.khat_no_l_torsion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerCompletionNoPrimeTorsion.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.kummerCompletion_no_prime_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.khat_no_l_torsion | exact GlobalTheory.KZ.BettiB.khat_no_l_torsion | (intros; apply GlobalTheory.KZ.BettiB.khat_no_l_torsion <;> assumption)
