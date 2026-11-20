import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltInjectiveAndDvdOfNormLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTiltUntiltInjectiveAndDvdOfNormLe.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧ ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  first | exact @GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | exact GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | (intros; apply GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le <;> assumption)
