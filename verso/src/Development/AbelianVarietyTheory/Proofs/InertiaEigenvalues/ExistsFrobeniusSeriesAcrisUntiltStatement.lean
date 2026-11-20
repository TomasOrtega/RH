import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntilt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSer.series_acris` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFrobeniusSeriesAcrisUntilt.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.exists_frobeniusSeries_acris_untilt : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  first | exact @GlobalTheory.PSer.series_acris | exact GlobalTheory.PSer.series_acris | (intros; apply GlobalTheory.PSer.series_acris <;> assumption)
