import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCapelliLeftComatrix.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.capelli_left_comatrix_qminor_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (j l : Fin (m + 1)), ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = if l = j then qdet E u else 0 := by
  first | exact @GlobalTheory.capelli_left_comatrix | exact GlobalTheory.capelli_left_comatrix | (intros; apply GlobalTheory.capelli_left_comatrix <;> assumption)
