import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLocalMatrixDivisionPointQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DivPtLocal.Count.card_locQ` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardLocalMatrixDivisionPointQuotient.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.card_localMatrixDivisionPointQuotient : ∀ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (N m n : ℕ), 0 < N → Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) = Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  first | exact @GlobalTheory.DivPtLocal.Count.card_locQ | exact GlobalTheory.DivPtLocal.Count.card_locQ | (intros; apply GlobalTheory.DivPtLocal.Count.card_locQ <;> assumption)
