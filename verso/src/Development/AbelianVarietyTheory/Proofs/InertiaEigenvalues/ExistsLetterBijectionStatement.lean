import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBijection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLetterBijection.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_letter_bijection' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P), ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)), Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  first | exact @GlobalTheory.RedFun.exists_letter_bijection | exact GlobalTheory.RedFun.exists_letter_bijection | (intros; apply GlobalTheory.RedFun.exists_letter_bijection <;> assumption)
