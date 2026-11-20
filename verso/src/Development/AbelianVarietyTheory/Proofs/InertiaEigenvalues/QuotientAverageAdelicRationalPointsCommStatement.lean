import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotientAverageAdelicRationalPointsComm.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.quotientAverage_adelicRationalPoints_comm : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι → Ad E) × (κ → Ad E) → ℂ), Per ((ratV E ι).prod (ratV E κ)) Φ → avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) = avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_comm | exact GlobalTheory.CuspGeneric.avg_comm | (intros; apply GlobalTheory.CuspGeneric.avg_comm <;> assumption)
