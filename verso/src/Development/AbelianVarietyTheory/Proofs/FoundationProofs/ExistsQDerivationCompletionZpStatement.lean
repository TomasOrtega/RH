import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQDerivationCompletionZp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.QDer.exists_qDer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsQDerivationCompletionZp.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.exists_qDerivation_completion_Zp : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := by
  first | exact @GlobalTheory.K5.QDer.exists_qDer | exact GlobalTheory.K5.QDer.exists_qDer | (intros; apply GlobalTheory.K5.QDer.exists_qDer <;> assumption)
