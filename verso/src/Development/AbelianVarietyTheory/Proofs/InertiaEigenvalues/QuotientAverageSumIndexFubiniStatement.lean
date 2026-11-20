import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageSumIndexFubini
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeneric.avg_sum_index` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotientAverageSumIndexFubini.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.quotientAverage_sum_index_fubini : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ → avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_sum_index | exact GlobalTheory.CuspGeneric.avg_sum_index | (intros; apply GlobalTheory.CuspGeneric.avg_sum_index <;> assumption)
