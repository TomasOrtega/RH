import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.GlobalFields.TateThesis.Gaussian
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory GroundTheory.Global Complex
open scoped Classical FourierTransform

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

def gP (a b : ℝ) : ℂ :=
  ((a : ℂ) + I * (b : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gP_eq (a b : ℝ) :
    gP a b = (a : ℂ) * realGaussian a * realGaussian b +
      I * (realGaussian a * ((b : ℂ) * realGaussian b)) := by
  unfold gP realGaussian
  rw [show -(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) =
      -(Real.pi : ℂ) * (a : ℂ) ^ 2 + -(Real.pi : ℂ) * (b : ℂ) ^ 2 by ring, Complex.exp_add]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_gP : Continuous fun p : ℝ × ℝ => gP p.1 p.2 := by
  unfold gP
  fun_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_charR (a : ℝ) : Continuous fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem integrable_charR_mul {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * f t) := by
  refine hf.norm.mono' ((continuous_charR a).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun t => by simp [Circle.norm_coe]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem integral_charR_even (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t = realGaussian a := by
  have h := congrFun fourier_realGaussian a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul] using h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem integral_charR_odd (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t) =
      -I * ((a : ℂ) * realGaussian a) := by
  have h := congrFun fourier_realGaussianOdd a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul, realGaussianOdd, realGaussian] using h

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_place (a b : ℝ) :
    ∫ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 = -I * gP a b := by
  have hsplit : ∀ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 =
      (((𝐞 (-(p.1 * a)) : Circle) : ℂ) * ((p.1 : ℂ) * realGaussian p.1)) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * realGaussian p.2) +
        I * ((((𝐞 (-(p.1 * a)) : Circle) : ℂ) * realGaussian p.1) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * ((p.2 : ℂ) * realGaussian p.2))) := by
    intro p
    rw [neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, gP_eq]
    ring
  have hodd : Integrable (fun t : ℝ => (t : ℂ) * realGaussian t) := integrable_realGaussianOdd
  simp_rw [hsplit]
  rw [Measure.volume_eq_prod,
    integral_add ((integrable_charR_mul hodd a).mul_prod (integrable_charR_mul integrable_realGaussian b))
      (((integrable_charR_mul integrable_realGaussian a).mul_prod (integrable_charR_mul hodd b)).const_mul I),
    integral_const_mul,
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t))
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * realGaussian t),
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t)
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t)),
    integral_charR_even, integral_charR_even, integral_charR_odd, integral_charR_odd, gP_eq]
  ring

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem selfDualMeasure_eq_volume [IsTotallyReal F] : selfDualMeasure F = volume := by
  rw [selfDualMeasure, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_smul]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isEmpty_complexPlaces [IsTotallyReal F] : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1) w.2⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isProbabilityMeasure_complexPart [IsTotallyReal F] :
    IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) := by
  haveI := isEmpty_complexPlaces F
  have h : (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac isEmptyElim := by
    rw [volume_pi, Measure.pi_of_empty]
  rw [h]
  infer_instance

def proj2 (x : Fin 2 → mixedSpace F) : {w : InfinitePlace F // IsReal w} → ℝ × ℝ :=
  fun w => ((x 0).1 w, (x 1).1 w)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem measurePreserving_proj2 [IsTotallyReal F] :
    MeasurePreserving (proj2 F) (GroundTheory.Automorphic.Adele2.mixedMeasure2 F) volume := by
  haveI := isProbabilityMeasure_complexPart F
  have h1 := measurePreserving_finTwoArrow (volume : Measure (mixedSpace F))
  have hf : MeasurePreserving (Prod.fst : mixedSpace F → ({w : InfinitePlace F // IsReal w} → ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod]
    exact measurePreserving_fst
  have h2 := hf.prod hf
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    {w : InfinitePlace F // IsReal w}).symm
  have h : proj2 F = (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ
      {w : InfinitePlace F // IsReal w}).symm ∘ Prod.map Prod.fst Prod.fst ∘
      MeasurableEquiv.finTwoArrow := by
    funext x w
    rfl
  rw [h, GroundTheory.Automorphic.Adele2.mixedMeasure2, selfDualMeasure_eq_volume]
  exact h3.comp (h2.comp h1)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arch_eq_prod [IsTotallyReal F] (x₀ x₁ : mixedSpace F) :
    arch (toR F x₀) (toR F x₁) = ∏ w : {w : InfinitePlace F // IsReal w}, gP (x₀.1 w) (x₁.1 w) :=
  (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _
    fun _ => rfl).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem char_pairing_eq_prod [IsTotallyReal F] (x y : Fin 2 → mixedSpace F) :
    ((𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) : Circle) : ℂ) =
      ∏ w : {w : InfinitePlace F // IsReal w},
        ((𝐞 (-((x 0).1 w * (y 0).1 w + (x 1).1 w * (y 1).1 w)) : Circle) : ℂ) := by
  haveI := isEmpty_complexPlaces F
  rw [GroundTheory.Automorphic.Adele2.mixedPairing2, Fin.sum_univ_two, mixedTraceForm_apply',
    mixedTraceForm_apply']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  exact map_prod Circle.coeHom _ _

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mixedFourier2_arch [IsTotallyReal F] (y : Fin 2 → mixedSpace F) :
    GroundTheory.Automorphic.Adele2.mixedFourier2 F (fun u => arch (toR F (u 0)) (toR F (u 1))) y =
      (-Complex.I) ^ Fintype.card (InfinitePlace F) * arch (toR F (y 0)) (toR F (y 1)) := by
  set f : {w : InfinitePlace F // IsReal w} → ℝ × ℝ → ℂ := fun w p =>
    ((𝐞 (-(p.1 * (y 0).1 w + p.2 * (y 1).1 w)) : Circle) : ℂ) * gP p.1 p.2 with hfdef
  have hpt : ∀ x : Fin 2 → mixedSpace F,
      𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) • arch (toR F (x 0)) (toR F (x 1)) =
        ∏ w, f w (proj2 F x w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, char_pairing_eq_prod, arch_eq_prod, ← Finset.prod_mul_distrib]
    rfl
  have hcont : Continuous fun z : {w : InfinitePlace F // IsReal w} → ℝ × ℝ => ∏ w, f w (z w) := by
    refine continuous_finsetProd _ fun w _ => ?_
    simp only [hfdef]
    refine Continuous.mul ?_ (continuous_gP.comp (continuous_apply w))
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  rw [GroundTheory.Automorphic.Adele2.mixedFourier2]
  simp_rw [hpt]
  rw [← integral_map (measurePreserving_proj2 F).aemeasurable hcont.aestronglyMeasurable,
    (measurePreserving_proj2 F).map_eq, integral_fintype_prod_volume_eq_prod f]
  simp only [hfdef, integral_place]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, arch_eq_prod,
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun v : InfinitePlace F => IsTotallyReal.isReal v)]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
