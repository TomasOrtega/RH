import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTiltUntiltToComplexPAdicBasicLaws.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧ (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧ (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧ (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  first | exact @GlobalTheory.PSer.Laws.sh_laws | exact GlobalTheory.PSer.Laws.sh_laws | (intros; apply GlobalTheory.PSer.Laws.sh_laws <;> assumption)
