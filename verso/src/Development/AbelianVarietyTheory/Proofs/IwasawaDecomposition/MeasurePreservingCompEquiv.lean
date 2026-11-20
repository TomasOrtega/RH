import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.UnifDens

/- English proof (translation)
Use `MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x i`. Use `MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)` as an intermediate fact. Simplify using `only [Equiv.symm_apply_apply] at this`.

Conclude with `this.symm`.
-/
theorem measurePreserving_comp_equiv {κ : Type} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℂ => fun i : κ => x (e i)) volume volume := by
  have := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  convert this using 1
  funext x i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

variable {ι : Type} [Fintype ι] {p q n : ℕ}

def flatL (h : Fintype.card (ι × Fin p × Fin q) = n) : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (ι × Fin p × Fin q → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv

/- English proof (translation)
Set `E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n` to `(PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv`. Establish `h1 : MeasurePreserving E' volume volume` using `GlobalTheory.measurePreserving_toLp_complex`. Establish `h2 : MeasurePreserving E'.symm volume volume` using `h1.symm`. Conclude with `(measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2`.
-/
theorem flatL_mp (h : Fintype.card (ι × Fin p × Fin q) = n) :
    MeasurePreserving (flatL h) volume volume := by
  let E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n :=
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv
  have h1 : MeasurePreserving E' volume volume := GlobalTheory.measurePreserving_toLp_complex
  have h2 : MeasurePreserving E'.symm volume volume := h1.symm
  exact (measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2

end GlobalTheory.UnifDens
