import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.FourierPush

/- English proof (translation)
Set `P` to `m.withDensity fun y => ENNReal.ofReal (G y)`. Set `P'` to `m.withDensity fun y => ENNReal.ofReal (-G y)`. Use `haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hG.2`. Use `haveI : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hG.neg.2`. Establish `hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I)` using `fun l => by fun_prop`.

Establish `hbd : ∀ (l : E →L[ℝ] ℝ) (y : Y), ‖Complex.exp ((l (p y) : ℂ) * Complex.I)‖ ≤ 1` using `fun l y => (Complex.norm_exp_ofReal_mul_I _).le`. Establish `hmeas : ∀ l : E →L[ℝ] ℝ, AEStronglyMeasurable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I)) m` using `fun l => ((hcont l).measurable.comp hp).aestronglyMeasurable`. Establish `e1 : ∀ l : E →L[ℝ] ℝ, charFunDual (P.map p) l = ∫ y, ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m`. Introduce `l`. Rewrite using `[charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]`.

Conclude with `integral_withDensity_eq_integral_smul₀ hG.aemeasurable.real_toNNReal _`. Establish `e2 : ∀ l : E →L[ℝ] ℝ, charFunDual (P'.map p) l = ∫ y, ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m`. Introduce `l`. Rewrite using `[charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]`. Conclude with `integral_withDensity_eq_integral_smul₀ hG.neg.aemeasurable.real_toNNReal _`.

Establish `hmap : P.map p = P'.map p`. Use `Measure.ext_of_charFunDual (funext fun l => ?_)` and prove the remaining obligations. Rewrite using `[e1, e2, ← sub_eq_zero]`. Establish `i1 : Integrable (fun y => ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m` using `hG.real_toNNReal.smul_of_top_left (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))`. Establish `i2 : Integrable (fun y => ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m` using `hG.neg.real_toNNReal.smul_of_top_left (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))`.

Rewrite using `[← integral_sub i1 i2, ← h l]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← sub_smul, Complex.real_smul, mul_comm]`. Use `congr 2`.

Simplify using `only [Real.coe_toNNReal']`. Break down `le_total 0 (G y) with h' | h'` into its components or cases. Rewrite using `[max_eq_left h', max_eq_right (by linarith)]; simp`. Rewrite using `[max_eq_right h', max_eq_left (by linarith)]; simp`. Establish `hval : ∀ f : Y → ℝ, ∫⁻ y in p ⁻¹' s, ENNReal.ofReal (f y) ∂m = (m.withDensity fun y => ENNReal.ofReal (f y)).map p s` using `fun f => by`.

Rewrite using `[Measure.map_apply hp hs, withDensity_apply _ (hp hs)]`. Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG.integrableOn, hval G, hval (fun y => -G y)]`. Express the relevant statement in the definitionally equal form `(P.map p s).toReal - (P'.map p s).toReal = 0`. Rewrite using `[hmap, sub_self]`.
-/
theorem real_case {Y : Type} [MeasurableSpace Y] (m : Measure Y) (G : Y → ℝ) (hG : Integrable G m)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * ((G y : ℝ) : ℂ) ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, G y ∂m = 0 := by
  let P := m.withDensity fun y => ENNReal.ofReal (G y)
  let P' := m.withDensity fun y => ENNReal.ofReal (-G y)
  haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hG.2
  haveI : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hG.neg.2
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hbd : ∀ (l : E →L[ℝ] ℝ) (y : Y), ‖Complex.exp ((l (p y) : ℂ) * Complex.I)‖ ≤ 1 :=
    fun l y => (Complex.norm_exp_ofReal_mul_I _).le
  have hmeas : ∀ l : E →L[ℝ] ℝ,
      AEStronglyMeasurable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
    fun l => ((hcont l).measurable.comp hp).aestronglyMeasurable
  have e1 : ∀ l : E →L[ℝ] ℝ, charFunDual (P.map p) l
      = ∫ y, ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.aemeasurable.real_toNNReal _
  have e2 : ∀ l : E →L[ℝ] ℝ, charFunDual (P'.map p) l
      = ∫ y, ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.neg.aemeasurable.real_toNNReal _
  have hmap : P.map p = P'.map p := by
    refine Measure.ext_of_charFunDual (funext fun l => ?_)
    rw [e1, e2, ← sub_eq_zero]
    have i1 : Integrable (fun y => ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    have i2 : Integrable (fun y => ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.neg.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    rw [← integral_sub i1 i2, ← h l]
    congr 1; funext y
    rw [← sub_smul, Complex.real_smul, mul_comm]
    congr 2
    simp only [Real.coe_toNNReal']
    rcases le_total 0 (G y) with h' | h'
    · rw [max_eq_left h', max_eq_right (by linarith)]; simp
    · rw [max_eq_right h', max_eq_left (by linarith)]; simp
  have hval : ∀ f : Y → ℝ, ∫⁻ y in p ⁻¹' s, ENNReal.ofReal (f y) ∂m
      = (m.withDensity fun y => ENNReal.ofReal (f y)).map p s := fun f => by
    rw [Measure.map_apply hp hs, withDensity_apply _ (hp hs)]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG.integrableOn, hval G,
    hval (fun y => -G y)]
  change (P.map p s).toReal - (P'.map p s).toReal = 0
  rw [hmap, sub_self]

/- English proof (translation)
Establish `hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I)` using `fun l => by fun_prop`. Establish `hI : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * F y) m` using `fun l => hF.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)`. Establish `hic : Integrable (fun y => (starRingEnd ℂ) (F y)) m`. Use `⟨hF.1.star, ?_⟩` and prove the remaining obligations. Simplify `hF.2` using `[HasFiniteIntegral]`.

Establish `hI' : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y)) m` using `fun l => hic.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)`. Establish `hconj : ∀ (l : E →L[ℝ] ℝ) (x : E), (starRingEnd ℂ) (Complex.exp ((((-l) x : ℝ) : ℂ) * Complex.I)) = Complex.exp (((l x : ℝ) : ℂ) * Complex.I)`. Introduce `l x`. Rewrite using `[← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Use `congr 1`.

Simplify using the standard rewrite rules. Establish `hc' : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y) ∂m = 0`. Introduce `l`. Use `congrArg (starRingEnd ℂ) (h (-l))` as an intermediate fact. Rewrite `this` using `[← integral_conj, map_zero]`.

Simplify `this` using `only [map_mul, hconj]`. Establish `hre : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).re : ℝ) : ℂ) ∂m = 0` using `fun l => by`. Simplify using `only [Complex.re_eq_add_conj, mul_div_assoc', mul_add]`. Rewrite using `[integral_div, integral_add (hI l) (hI' l), h l, hc' l]`. Simplify using the standard rewrite rules.

Establish `him : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).im : ℝ) : ℂ) ∂m = 0` using `fun l => by`. Simplify using `only [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]`. Rewrite using `[integral_div, integral_sub (hI l) (hI' l), h l, hc' l]`. Simplify using the standard rewrite rules. Establish `h1` using `real_case m (fun y => (F y).re) hF.re p hp hre s hs`.

Establish `h2` using `real_case m (fun y => (F y).im) hF.im p hp him s hs`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.zero_re, ← h1]`. Conclude with `(integral_re hF.integrableOn).symm`. Rewrite using `[Complex.zero_im, ← h2]`.

Conclude with `(integral_im hF.integrableOn).symm`.
-/
theorem setIntegral_preimage_eq_zero (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ)
    (hF : Integrable F m) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hI : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * F y) m :=
    fun l => hF.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hic : Integrable (fun y => (starRingEnd ℂ) (F y)) m := by
    refine ⟨hF.1.star, ?_⟩
    simpa [HasFiniteIntegral] using hF.2
  have hI' : ∀ l : E →L[ℝ] ℝ,
      Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y)) m :=
    fun l => hic.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hconj : ∀ (l : E →L[ℝ] ℝ) (x : E),
      (starRingEnd ℂ) (Complex.exp ((((-l) x : ℝ) : ℂ) * Complex.I)) = Complex.exp (((l x : ℝ) : ℂ) * Complex.I) := by
    intro l x
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    simp
  have hc' : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y) ∂m = 0 := by
    intro l
    have := congrArg (starRingEnd ℂ) (h (-l))
    rw [← integral_conj, map_zero] at this
    simpa only [map_mul, hconj] using this
  have hre : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).re : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.re_eq_add_conj, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (hI l) (hI' l), h l, hc' l]; simp
  have him : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).im : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]
    rw [integral_div, integral_sub (hI l) (hI' l), h l, hc' l]; simp
  have h1 := real_case m (fun y => (F y).re) hF.re p hp hre s hs
  have h2 := real_case m (fun y => (F y).im) hF.im p hp him s hs
  apply Complex.ext
  · rw [Complex.zero_re, ← h1]
    exact (integral_re hF.integrableOn).symm
  · rw [Complex.zero_im, ← h2]
    exact (integral_im hF.integrableOn).symm

end GlobalTheory.FourierPush

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

/- English proof (translation)
The claim follows from `GlobalTheory.FourierPush.setIntegral_preimage_eq_zero`.
-/
example : ∀ (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : Y → E), Measurable p → (∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0) → ∀ s : Set E, MeasurableSet s → ∫ y in p ⁻¹' s, F y ∂m = 0 :=
  GlobalTheory.FourierPush.setIntegral_preimage_eq_zero
