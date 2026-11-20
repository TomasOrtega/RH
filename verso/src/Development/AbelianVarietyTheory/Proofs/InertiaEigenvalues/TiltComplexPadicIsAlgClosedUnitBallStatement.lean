import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBall
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import GroundTheory.PAdicHodge.TiltField
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTiltComplexPadicIsAlgClosedUnitBall.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.tilt_complexPadic_isAlgClosed_unitBall : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l) ∧ ∃ ι : Fl l →+* (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), (∀ x, GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l (ι x) = sh x) ∧ (∀ z : (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  first | exact @GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall | exact GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall | (intros; apply GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall <;> assumption)
