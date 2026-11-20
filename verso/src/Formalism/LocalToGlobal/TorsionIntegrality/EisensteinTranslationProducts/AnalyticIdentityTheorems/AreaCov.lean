import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.F

namespace AreaCov

/- English proof (translation)
Establish `hset : ZSpan.fundamentalDomain Complex.basisOneI = Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)`. Use extensionality with `z`. Rewrite using `[Set.mem_preimage]`. Express the relevant statement in the definitionally equal form `_ ↔ (z.re, z.im) ∈ Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1`. Simplify using `[ZSpan.mem_fundamentalDomain, Fin.forall_fin_two, Complex.coe_basisOneI_repr, Set.mem_prod]`.

Use `show (volume (ZSpan.fundamentalDomain Complex.basisOneI)).toReal = 1`. Rewrite using `[hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]`. Simplify using the standard rewrite rules.
-/
lemma volume_real_fundamentalDomain_basisOneI :
    (volume : Measure ℂ).real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  have hset : ZSpan.fundamentalDomain Complex.basisOneI =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    rw [Set.mem_preimage]
    change _ ↔ (z.re, z.im) ∈ Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1
    simp [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two, Complex.coe_basisOneI_repr, Set.mem_prod]
  show (volume (ZSpan.fundamentalDomain Complex.basisOneI)).toReal = 1
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
  simp

/- English proof (translation)
Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `[Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma det_periods (L : PeriodPair) :
    Complex.basisOneI.det ((↑) ∘ L.latticeBasis) = (conj L.ω₁ * L.ω₂).im := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.mul_im]
  ring

end AreaCov

/- English proof (translation)
Introduce `L`. Rewrite using `[ZLattice.covolume_eq_det_mul_measureReal L.lattice volume L.latticeBasis Complex.basisOneI, Formalism.L2.Th1.F.AreaCov.det_periods, Formalism.L2.Th1.F.AreaCov.volume_real_fundamentalDomain_basisOneI, mul_one]`. Both sides reduce to the same expression.
-/
theorem area_covolume : AreaCovolume := by
  intro L
  rw [ZLattice.covolume_eq_det_mul_measureReal L.lattice volume L.latticeBasis Complex.basisOneI,
    Formalism.L2.Th1.F.AreaCov.det_periods, Formalism.L2.Th1.F.AreaCov.volume_real_fundamentalDomain_basisOneI, mul_one]
  rfl

end Formalism.L2.Th1.F
