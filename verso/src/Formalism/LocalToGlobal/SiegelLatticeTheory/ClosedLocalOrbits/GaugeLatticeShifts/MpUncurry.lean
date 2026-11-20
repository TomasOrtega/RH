import Mathlib

open MeasureTheory Set

noncomputable section

namespace Formalism.MainNotions.S.Gauge

/- English proof (translation)
Use `⟨(MeasurableEquiv.curry κ (Fin 2) ℝ).symm.measurable, ?_⟩` and prove the remaining obligations. Use `(Measure.pi_eq (fun s _ => ?_)).symm` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply]`. Establish `hpre : ((MeasurableEquiv.curry κ (Fin 2) ℝ).symm) ⁻¹' (univ.pi s) = univ.pi (fun k => univ.pi (fun i => s (k, i)))`. Use extensionality with `x`.

Simplify using `[MeasurableEquiv.coe_curry_symm, Function.uncurry]`. Rewrite using `[hpre, volume_pi_pi]`. Repeatedly rewrite using `[volume_pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`.
-/
theorem mp_uncurry (κ : Type*) [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry κ (Fin 2) ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry κ (Fin 2) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : ((MeasurableEquiv.curry κ (Fin 2) ℝ).symm) ⁻¹' (univ.pi s) =
      univ.pi (fun k => univ.pi (fun i => s (k, i))) := by
    ext x; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]

/- English proof (translation)
Establish `h1` using `PiLp.volume_preserving_ofLp (ι := κ × Fin 2)`. Establish `h2` using `MeasurePreserving.symm _ (mp_uncurry κ)`. Establish `h3` using `volume_preserving_pi (fun _ : κ => Complex.volume_preserving_equiv_pi.symm)`. Conclude with `(h3.comp h2).comp h1`.
-/
theorem mp_cF (κ : Type*) [Fintype κ] :
    MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
      volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (ι := κ × Fin 2)
  have h2 := MeasurePreserving.symm _ (mp_uncurry κ)
  have h3 := volume_preserving_pi (fun _ : κ => Complex.volume_preserving_equiv_pi.symm)
  exact (h3.comp h2).comp h1

end Formalism.MainNotions.S.Gauge
