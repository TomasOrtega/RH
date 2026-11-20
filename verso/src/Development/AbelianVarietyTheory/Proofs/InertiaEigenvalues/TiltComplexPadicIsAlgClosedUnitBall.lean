import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import GroundTheory.PAdicHodge.TiltField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

/- English proof (translation)
Introduce `l _`. Take `⟨e, he⟩` from `exists_flEquiv_untilt l`. Establish `hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l)` using `(GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1`. Use `⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩` and prove the remaining obligations. Set `e' : Formalism.BasicNotions.Loc.Cb l ≃+* Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l` to `IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e`.

Conclude with `IsAlgClosed.of_ringEquiv _ _ e'`. Introduce `x`. Rewrite using `[RingHom.comp_apply, tiltSharp_algebraMap]`. Conclude with `he x`. Introduce `z hz`.

Take `⟨a, rfl⟩` from `norm_le_one_iff_exists_algebraMap.1 hz`. Conclude with `⟨e.symm a, by simp⟩`.
-/
theorem tilt_isAlgClosed_and_unitBall : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l) ∧ ∃ ι : Fl l →+* (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), (∀ x, GroundTheory.PAdicHodge.tiltSharp ℂ_[l] l (ι x) = sh x) ∧ (∀ z : (Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l), ‖z‖ ≤ 1 → ∃ x, ι x = z) := by
  intro l _
  obtain ⟨e, he⟩ := exists_flEquiv_untilt l
  have hC : IsAlgClosed (Formalism.BasicNotions.Loc.Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  refine ⟨?_, (algebraMap (PreTilt (normInteger ℂ_[l]) l) _).comp (e : Fl l →+* _), ?_, ?_⟩
  · let e' : Formalism.BasicNotions.Loc.Cb l ≃+* Tilt ℂ_[l] NormedField.valuation (GroundTheory.PAdicHodge.normInteger ℂ_[l]) GroundTheory.PAdicHodge.normInteger_integers l :=
      IsFractionRing.ringEquivOfRingEquiv (A := Formalism.BasicNotions.Loc.OCb l) (B := PreTilt (normInteger ℂ_[l]) l) e
    exact IsAlgClosed.of_ringEquiv _ _ e'
  · intro x
    rw [RingHom.comp_apply, tiltSharp_algebraMap]
    exact he x
  · intro z hz
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
    exact ⟨e.symm a, by simp⟩

end GlobalTheory.PSer
