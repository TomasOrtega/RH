import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelThird

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.unitMultiplierModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

/- English proof (translation)
Establish `hc : c ∈ Submonoid.unitSphere ℂ` using `by simp [Submonoid.unitSphere, h]`. Establish `key` using `(rotation (⟨c, hc⟩ : Circle)).measurePreserving`. Establish `e : (fun z : ℂ => c * z) = rotation (⟨c, hc⟩ : Circle)`. Use function extensionality and compare the values at `z`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `key`.
-/
theorem mul_unit_mp (c : ℂ) (h : ‖c‖ = 1) : MeasurePreserving (fun z : ℂ => c * z) volume volume := by
  have hc : c ∈ Submonoid.unitSphere ℂ := by simp [Submonoid.unitSphere, h]
  have key := (rotation (⟨c, hc⟩ : Circle)).measurePreserving
  have e : (fun z : ℂ => c * z) = rotation (⟨c, hc⟩ : Circle) := by
    funext z; rfl
  rw [e]
  exact key

variable (d : Fin (r + 1) → ℂ)

/- English proof (translation)
Establish `inj : Function.Injective (sw pN)`. Introduce `a b hab`. Simplify using `[sw] at hab`. Conclude with `Subtype.ext (Prod.ext hab.2 hab.1)`. Set `e : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W` to `Equiv.ofBijective (sw pN) (Finite.injective_iff_bijective.mp inj)`.

Establish `hG` using `volume_measurePreserving_piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm`. Establish `h : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, MeasurePreserving (fun z : ℂ => d (W q.1.1) / d (W q.1.2) * star z) volume volume`. Introduce `q`. Establish `hu : ‖d (W q.1.1) / d (W q.1.2)‖ = 1`. Rewrite using `[norm_div, hdm q, div_self]`.

Conclude with `norm_ne_zero_iff.mpr (hd _)`. Conclude with `(mul_unit_mp _ hu).comp Complex.conjLIE.measurePreserving`. Establish `hF` using `volume_preserving_pi h`. Establish `heq : Rm pN d = (fun (a : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i : Formalism.FourierDecayAlt.C2.Lstidx W) => d (W i.1.1) / d (W i.1.2) * star (a i)) ∘ (MeasurableEquiv.piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm)`. Use function extensionality and compare the values at `x q`.

Simplify using `only [Rm, Function.comp_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]`. Simplify using `[e]`. Rewrite using `[heq]`. Conclude with `hF.comp hG`.
-/
theorem Rm_mp (hd : ∀ a, d a ≠ 0) (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, ‖d (W q.1.1)‖ = ‖d (W q.1.2)‖) :
    MeasurePreserving (Rm pN d) volume volume := by
  have inj : Function.Injective (sw pN) := by
    intro a b hab
    simp [sw] at hab
    exact Subtype.ext (Prod.ext hab.2 hab.1)
  let e : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W :=
    Equiv.ofBijective (sw pN) (Finite.injective_iff_bijective.mp inj)
  have hG := volume_measurePreserving_piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm
  have h : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W,
      MeasurePreserving (fun z : ℂ => d (W q.1.1) / d (W q.1.2) * star z) volume volume := by
    intro q
    have hu : ‖d (W q.1.1) / d (W q.1.2)‖ = 1 := by
      rw [norm_div, hdm q, div_self]
      exact norm_ne_zero_iff.mpr (hd _)
    exact (mul_unit_mp _ hu).comp Complex.conjLIE.measurePreserving
  have hF := volume_preserving_pi h
  have heq : Rm pN d = (fun (a : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i : Formalism.FourierDecayAlt.C2.Lstidx W) =>
      d (W i.1.1) / d (W i.1.2) * star (a i)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm) := by
    funext x q
    simp only [Rm, Function.comp_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp [e]
  rw [heq]
  exact hF.comp hG

end Formalism.L2.SG.unitMultiplierModel

end
