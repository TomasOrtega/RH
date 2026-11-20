import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotientAverageUnipotentBlockColumnTransformEqZe.lean&line=239#L239)
-/
theorem _root_.GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ r, 0 < r → r ≤ m → ∀ g : GA E a, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero | exact GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero <;> assumption)
