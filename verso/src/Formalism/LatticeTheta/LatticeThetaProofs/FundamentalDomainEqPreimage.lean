import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

abbrev boxIco (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

/- English proof (translation)
Rewrite using `[volume_pi_pi]`. Simplify using `[Real.volume_Ico]`.
-/
theorem volume_boxIco : volume (boxIco ι) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Ico]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]`.
-/
theorem fundamentalDomain_eq_preimage (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]

/- English proof (translation)
Set `ψ : V ≃ᵐ (ι → ℝ)` to `e.equivFunL.toHomeomorph.toMeasurableEquiv`. Establish `hψ : (ψ : V → ι → ℝ) = e.equivFunL` using `rfl`. Use `set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef`. Use `haveI : ν.IsAddHaarMeasure := by`. Rewrite using `[hνdef, hψ]`.

Conclude with `e.equivFunL.isAddHaarMeasure_map volume`. Establish `hν : ν = ν.addHaarScalarFactor volume • volume` using `Measure.isAddLeftInvariant_eq_smul ν volume`. Establish `hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e)`. Rewrite using `[hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]`. Establish `hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e)`.

Rewrite using `[← hbox]`. Use `conv_rhs => rw [hν]`. Simplify using `[volume_boxIco]`. Establish `hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν`. Rewrite using `[hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]`.

Simplify using `only [hψ, ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc, ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]`.
-/
theorem integral_fundamentalDomain_eq (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by
  let ψ : V ≃ᵐ (ι → ℝ) := e.equivFunL.toHomeomorph.toMeasurableEquiv
  have hψ : (ψ : V → ι → ℝ) = e.equivFunL := rfl
  set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef
  haveI : ν.IsAddHaarMeasure := by
    rw [hνdef, hψ]; exact e.equivFunL.isAddHaarMeasure_map volume
  have hν : ν = ν.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e) := by
    rw [hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]
  have hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e) := by
    rw [← hbox]
    conv_rhs => rw [hν]
    simp [volume_boxIco]
  have hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν := by
    rw [hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]
    simp only [hψ, ContinuousLinearEquiv.symm_apply_apply]
  rw [hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc,
    ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]

end Formalism.H
