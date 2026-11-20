import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSer.sh_add_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTiltUntiltAddEstimateLe.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.tiltUntilt_add_estimate_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  first | exact @GlobalTheory.PSer.sh_add_le | exact GlobalTheory.PSer.sh_add_le | (intros; apply GlobalTheory.PSer.sh_add_le <;> assumption)
