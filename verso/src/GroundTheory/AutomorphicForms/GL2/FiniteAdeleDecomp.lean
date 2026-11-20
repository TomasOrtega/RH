import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

namespace GroundTheory.Automorphic.GodementSection

open NumberField IsDedekindDomain MeasureTheory Filter Topology GroundTheory.Global GroundTheory.LocalField
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise ValuativeRel

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section AtS

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def adeleAtS : FiniteAdeleRing (𝓞 K) K →+ ((v : S) → v.1.adicCompletion K) where
  toFun x v := x v.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adeleAtS_apply (x : FiniteAdeleRing (𝓞 K) K) (v : S) : adeleAtS S x v = x v.1 := rfl

/- English proof (translation)
The claim follows from `continuous_pi fun v ↦ RestrictedProduct.continuous_eval v.1`.
-/
theorem continuous_adeleAtS : Continuous (adeleAtS (K := K) S) :=
  continuous_pi fun v ↦ RestrictedProduct.continuous_eval v.1

/- English proof (translation)
The claim follows from `(continuous_adeleAtS S).measurable`.
-/
theorem measurable_adeleAtS : Measurable (adeleAtS (K := K) S) :=
  (continuous_adeleAtS S).measurable

def adeleSingleS : ((v : S) → v.1.adicCompletion K) →+ FiniteAdeleRing (𝓞 K) K where
  toFun a := ∑ v : S, finiteAdeleSingleAdd v.1 (a v)
  map_zero' := by simp
  map_add' a a' := by
    simp only [Pi.add_apply, map_add]
    exact Finset.sum_add_distrib

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w.1 = a w`. Rewrite using `[show (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w.1 = ∑ v : S, (finiteAdeleSingleAdd v.1 (a v)) w.1 from map_sum (RestrictedProduct.evalAddMonoidHom _ w.1) _ _]`. Rewrite using `[Finset.sum_eq_single w]`. Conclude with `finiteAdeleSingleAdd_apply_self w.1 (a w)`. Introduce `u _ hu`.

Conclude with `finiteAdeleSingleAdd_apply_of_ne (fun h ↦ hu (Subtype.ext h).symm) _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`.
-/
theorem adeleSingleS_apply_of_mem (a : (v : S) → v.1.adicCompletion K) (w : S) :
    adeleSingleS S a w.1 = a w := by
  classical
  change (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w.1 = a w
  rw [show (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w.1 =
      ∑ v : S, (finiteAdeleSingleAdd v.1 (a v)) w.1 from
    map_sum (RestrictedProduct.evalAddMonoidHom _ w.1) _ _]
  rw [Finset.sum_eq_single w]
  · exact finiteAdeleSingleAdd_apply_self w.1 (a w)
  · intro u _ hu
    exact finiteAdeleSingleAdd_apply_of_ne (fun h ↦ hu (Subtype.ext h).symm) _
  · intro h
    exact absurd (Finset.mem_univ w) h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w = 0`. Rewrite using `[show (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w = ∑ v : S, (finiteAdeleSingleAdd v.1 (a v)) w from map_sum (RestrictedProduct.evalAddMonoidHom _ w) _ _]`. Conclude with `Finset.sum_eq_zero fun u _ ↦ finiteAdeleSingleAdd_apply_of_ne (fun h ↦ hw (by rw [h]; exact u.2)) _`.
-/
theorem adeleSingleS_apply_of_notMem (a : (v : S) → v.1.adicCompletion K)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) : adeleSingleS S a w = 0 := by
  change (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w = 0
  rw [show (∑ v : S, finiteAdeleSingleAdd v.1 (a v)) w =
      ∑ v : S, (finiteAdeleSingleAdd v.1 (a v)) w from
    map_sum (RestrictedProduct.evalAddMonoidHom _ w) _ _]
  exact Finset.sum_eq_zero fun u _ ↦
    finiteAdeleSingleAdd_apply_of_ne (fun h ↦ hw (by rw [h]; exact u.2)) _

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[map_add, Pi.add_apply, Pi.add_apply]`. Simplify using `only [adeleAtS_apply, adeleSingleS_apply_of_mem]`.
-/
theorem adeleAtS_adeleSingleS_add (a : (v : S) → v.1.adicCompletion K)
    (x : FiniteAdeleRing (𝓞 K) K) : adeleAtS S (adeleSingleS S a + x) = a + adeleAtS S x := by
  funext w
  rw [map_add, Pi.add_apply, Pi.add_apply]
  simp only [adeleAtS_apply, adeleSingleS_apply_of_mem]

/- English proof (translation)
The claim follows from `hG _ _ fun w hw ↦ by rw [show (adeleSingleS S a + x) w = adeleSingleS S a w + x w from rfl, adeleSingleS_apply_of_notMem S a hw, zero_add]`.
-/
theorem apply_adeleSingleS_add {E : Type*} {G : FiniteAdeleRing (𝓞 K) K → E}
    (hG : ∀ x x', (∀ w ∉ S, x w = x' w) → G x = G x')
    (a : (v : S) → v.1.adicCompletion K) (x : FiniteAdeleRing (𝓞 K) K) :
    G (adeleSingleS S a + x) = G x :=
  hG _ _ fun w hw ↦ by
    rw [show (adeleSingleS S a + x) w = adeleSingleS S a w + x w from rfl,
      adeleSingleS_apply_of_notMem S a hw, zero_add]

def intS : Set ((v : S) → v.1.adicCompletion K) :=
  Set.univ.pi fun v ↦ (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K))

/- English proof (translation)
The claim follows from `Valued.isOpen_integer _`.
-/
theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_integer _

/- English proof (translation)
The claim follows from `isOpen_set_pi Set.finite_univ fun v _ ↦ isOpen_adicCompletionIntegers v.1`.
-/
theorem isOpen_intS : IsOpen (intS (K := K) S) :=
  isOpen_set_pi Set.finite_univ fun v _ ↦ isOpen_adicCompletionIntegers v.1

/- English proof (translation)
The claim follows from `(isOpen_intS S).measurableSet`.
-/
theorem measurableSet_intS : MeasurableSet (intS (K := K) S) :=
  (isOpen_intS S).measurableSet

abbrev haarS : Measure ((v : S) → v.1.adicCompletion K) :=
  Measure.pi fun v ↦ haarIntegers (v.1.adicCompletion K)

/- English proof (translation)
Use extensionality with `x`. Conclude with `mem_valuationInteger_iff v x`.
-/
theorem coe_valuationInteger_eq (v : HeightOneSpectrum (𝓞 K)) :
    (𝒪[v.adicCompletion K] : Set (v.adicCompletion K)) = v.adicCompletionIntegers K := by
  ext x
  exact mem_valuationInteger_iff v x

/- English proof (translation)
Rewrite using `[intS, Measure.pi_pi]`. Use `Finset.prod_eq_one fun v _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← coe_valuationInteger_eq]`. Conclude with `haarIntegers_integers`.
-/
theorem haarS_intS : haarS (K := K) S (intS S) = 1 := by
  rw [intS, Measure.pi_pi]
  refine Finset.prod_eq_one fun v _ ↦ ?_
  rw [← coe_valuationInteger_eq]
  exact haarIntegers_integers

def addAwayImageS (g : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞) : Measure ((v : S) → v.1.adicCompletion K) :=
  Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity g)

variable {S}

/- English proof (translation)
Rewrite using `[addAwayImageS, Measure.map_apply (measurable_adeleAtS S) hA, withDensity_apply _ (measurable_adeleAtS S hA), lintegral_indicator (measurable_adeleAtS S hA)]`.
-/
theorem addAwayImageS_apply (g : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞)
    {A : Set ((v : S) → v.1.adicCompletion K)} (hA : MeasurableSet A) :
    addAwayImageS S g A = ∫⁻ x, (adeleAtS S ⁻¹' A).indicator g x ∂finiteAdeleMeasure K := by
  rw [addAwayImageS, Measure.map_apply (measurable_adeleAtS S) hA,
    withDensity_apply _ (measurable_adeleAtS S hA), lintegral_indicator (measurable_adeleAtS S hA)]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a`. Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_const_add a) hA, addAwayImageS_apply g (measurable_const_add a hA), addAwayImageS_apply g hA, ← lintegral_add_left_eq_self _ (adeleSingleS S (-a))]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Establish `h : adeleAtS S (adeleSingleS S (-a) + x) = -a + adeleAtS S x` using `adeleAtS_adeleSingleS_add S (-a) x`. Simplify using `only [Set.indicator_apply, Set.mem_preimage, h, add_neg_cancel_left, hinv]`.
-/
theorem isAddLeftInvariant_addAwayImageS {g : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞}
    (hinv : ∀ a x, g (adeleSingleS S a + x) = g x) : (addAwayImageS S g).IsAddLeftInvariant := by
  constructor
  intro a
  ext A hA
  rw [Measure.map_apply (measurable_const_add a) hA, addAwayImageS_apply g (measurable_const_add a hA),
    addAwayImageS_apply g hA, ← lintegral_add_left_eq_self _ (adeleSingleS S (-a))]
  congr 1
  funext x
  have h : adeleAtS S (adeleSingleS S (-a) + x) = -a + adeleAtS S x :=
    adeleAtS_adeleSingleS_add S (-a) x
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, h, add_neg_cancel_left, hinv]

/- English proof (translation)
Use `isAddLeftInvariant_addAwayImageS hinv` as an intermediate fact. Use `⟨fun C hC ↦ ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun a : C ↦ (a : (v : S) → v.1.adicCompletion K) +ᵥ intS S) (fun a ↦ (isOpen_intS S).vadd _) (fun c hc ↦ Set.mem_iUnion.2 ⟨⟨c, hc⟩, Set.mem_vadd_set.2 ⟨0, fun v _ ↦ zero_mem (v.1.adicCompletionIntegers K), add_zero c⟩⟩)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isFiniteMeasureOnCompacts_addAwayImageS {g : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞}
    (hinv : ∀ a x, g (adeleSingleS S a + x) = g x) (hc : addAwayImageS S g (intS S) ≠ ∞) :
    IsFiniteMeasureOnCompacts (addAwayImageS S g) := by
  have := isAddLeftInvariant_addAwayImageS hinv
  refine ⟨fun C hC ↦ ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun a : C ↦ (a : (v : S) → v.1.adicCompletion K) +ᵥ intS S)
    (fun a ↦ (isOpen_intS S).vadd _)
    (fun c hc ↦ Set.mem_iUnion.2 ⟨⟨c, hc⟩, Set.mem_vadd_set.2
      ⟨0, fun v _ ↦ zero_mem (v.1.adicCompletionIntegers K), add_zero c⟩⟩)
  calc addAwayImageS S g C
      ≤ addAwayImageS S g (⋃ i ∈ t, (i : (v : S) → v.1.adicCompletion K) +ᵥ intS S) :=
        measure_mono ht
    _ ≤ ∑ i ∈ t, addAwayImageS S g ((i : (v : S) → v.1.adicCompletion K) +ᵥ intS S) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ t, addAwayImageS S g (intS S) :=
        Finset.sum_congr rfl fun i _ ↦ measure_vadd _ _ _
    _ < ∞ := ENNReal.sum_lt_top.2 fun _ _ ↦ hc.lt_top

/- English proof (translation)
Use `isAddLeftInvariant_addAwayImageS hinv` as an intermediate fact. Use `isFiniteMeasureOnCompacts_addAwayImageS hinv hc` as an intermediate fact. Establish `h` using `Measure.isAddLeftInvariant_eq_smul (addAwayImageS S g) (haarS S)`. Use `set c := Measure.addHaarScalarFactor (addAwayImageS S g) (haarS S)`. Establish `hU : addAwayImageS S g (intS S) = (c : ℝ≥0∞)` using `by conv_lhs => rw [h]`.

Rewrite using `[Measure.smul_apply, haarS_intS, ENNReal.smul_def, smul_eq_mul, mul_one]`. Rewrite using `[hU]`. Use `conv_lhs => rw [h]`. Use extensionality with `A _`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`.
-/
theorem addAwayImageS_eq_smul {g : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞}
    (hinv : ∀ a x, g (adeleSingleS S a + x) = g x) (hc : addAwayImageS S g (intS S) ≠ ∞) :
    addAwayImageS S g = addAwayImageS S g (intS S) • haarS S := by
  have := isAddLeftInvariant_addAwayImageS hinv
  have := isFiniteMeasureOnCompacts_addAwayImageS hinv hc
  have h := Measure.isAddLeftInvariant_eq_smul (addAwayImageS S g) (haarS S)
  set c := Measure.addHaarScalarFactor (addAwayImageS S g) (haarS S)
  have hU : addAwayImageS S g (intS S) = (c : ℝ≥0∞) := by
    conv_lhs => rw [h]
    rw [Measure.smul_apply, haarS_intS, ENNReal.smul_def, smul_eq_mul, mul_one]
  rw [hU]
  conv_lhs => rw [h]
  ext A _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end AtS

section Integrals

variable {S : Finset (HeightOneSpectrum (𝓞 K))}

/- English proof (translation)
Use `set gE : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞ := fun x ↦ (g x : ℝ≥0∞) with hgE`. Use `set I : ℝ := ∫ x, (adeleAtS S ⁻¹' intS S).indicator (fun x ↦ (g x : ℝ)) x ∂finiteAdeleMeasure K with hI`. Establish `hinvE : ∀ a x, gE (adeleSingleS S a + x) = gE x` using `fun a x ↦ by simp only [hgE, hinv]`. Establish `hcI : addAwayImageS S gE (intS S) = ENNReal.ofReal I`. Rewrite using `[addAwayImageS_apply gE (measurableSet_intS S), hI, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun x ↦ Set.indicator_nonneg (fun x _ ↦ (g x).2) x)]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Set.indicator_apply, hgE]`. Use `split_ifs`. Conclude with `(ENNReal.ofReal_coe_nnreal).symm`.

Conclude with `ENNReal.ofReal_zero.symm`. Establish `hc : addAwayImageS S gE (intS S) ≠ ∞` using `by rw [hcI]; exact ENNReal.ofReal_ne_top`. Establish `e` using `addAwayImageS_eq_smul hinvE hc`. Rewrite `e` using `[hcI]`. Establish `hmap : Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE) = ENNReal.ofReal I • haarS S` using `e`.

Establish `hFm : AEStronglyMeasurable F (Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE))`. Rewrite using `[hmap]`. Conclude with `hF.aestronglyMeasurable.smul_measure _`. Establish `hpt : ∀ x, F (adeleAtS S x) * ((g x : ℝ) : ℂ) = g x • F (adeleAtS S x)` using `fun x ↦ by`. Rewrite using `[NNReal.smul_def, Complex.real_smul, mul_comm]`.

Repeatedly rewrite using `[hpt]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← integrable_withDensity_iff_integrable_smul hg]`. Establish `: Integrable F (Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE))`. Rewrite using `[hmap]`.

Conclude with `hF.smul_measure ENNReal.ofReal_ne_top`. Conclude with `(integrable_map_measure hFm (measurable_adeleAtS S).aemeasurable).1 this`. Rewrite using `[← integral_withDensity_eq_integral_smul hg, ← integral_map (measurable_adeleAtS S).aemeasurable hFm, hmap, integral_smul_measure, ENNReal.toReal_ofReal (hI ▸ integral_nonneg fun x ↦ Set.indicator_nonneg (fun x _ ↦ (g x).2) x), Complex.real_smul, mul_comm]`.
-/
theorem integral_comp_adeleAtS_mul_nnreal {g : FiniteAdeleRing (𝓞 K) K → ℝ≥0}
    (hg : Measurable g) (hinv : ∀ a x, g (adeleSingleS S a + x) = g x)
    (hgi : Integrable ((adeleAtS S ⁻¹' intS S).indicator fun x ↦ (g x : ℝ)) (finiteAdeleMeasure K))
    {F : ((v : S) → v.1.adicCompletion K) → ℂ} (hF : Integrable F (haarS S)) :
    Integrable (fun x ↦ F (adeleAtS S x) * ((g x : ℝ) : ℂ)) (finiteAdeleMeasure K) ∧
      ∫ x, F (adeleAtS S x) * ((g x : ℝ) : ℂ) ∂finiteAdeleMeasure K =
        (∫ a, F a ∂haarS S) *
          ((∫ x, (adeleAtS S ⁻¹' intS S).indicator (fun x ↦ (g x : ℝ)) x
            ∂finiteAdeleMeasure K : ℝ) : ℂ) := by
  set gE : FiniteAdeleRing (𝓞 K) K → ℝ≥0∞ := fun x ↦ (g x : ℝ≥0∞) with hgE
  set I : ℝ := ∫ x, (adeleAtS S ⁻¹' intS S).indicator (fun x ↦ (g x : ℝ)) x
    ∂finiteAdeleMeasure K with hI
  have hinvE : ∀ a x, gE (adeleSingleS S a + x) = gE x := fun a x ↦ by simp only [hgE, hinv]
  have hcI : addAwayImageS S gE (intS S) = ENNReal.ofReal I := by
    rw [addAwayImageS_apply gE (measurableSet_intS S), hI,
      ofReal_integral_eq_lintegral_ofReal hgi
        (Eventually.of_forall fun x ↦ Set.indicator_nonneg (fun x _ ↦ (g x).2) x)]
    congr 1
    funext x
    classical
    simp only [Set.indicator_apply, hgE]
    split_ifs
    · exact (ENNReal.ofReal_coe_nnreal).symm
    · exact ENNReal.ofReal_zero.symm
  have hc : addAwayImageS S gE (intS S) ≠ ∞ := by rw [hcI]; exact ENNReal.ofReal_ne_top
  have e := addAwayImageS_eq_smul hinvE hc
  rw [hcI] at e
  have hmap : Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE) =
      ENNReal.ofReal I • haarS S := e
  have hFm : AEStronglyMeasurable F
      (Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable.smul_measure _
  have hpt : ∀ x, F (adeleAtS S x) * ((g x : ℝ) : ℂ) = g x • F (adeleAtS S x) := fun x ↦ by
    rw [NNReal.smul_def, Complex.real_smul, mul_comm]
  simp_rw [hpt]
  constructor
  · rw [← integrable_withDensity_iff_integrable_smul hg]
    have : Integrable F (Measure.map (adeleAtS S) ((finiteAdeleMeasure K).withDensity gE)) := by
      rw [hmap]
      exact hF.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure hFm (measurable_adeleAtS S).aemeasurable).1 this
  · rw [← integral_withDensity_eq_integral_smul hg,
      ← integral_map (measurable_adeleAtS S).aemeasurable hFm, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (hI ▸ integral_nonneg fun x ↦ Set.indicator_nonneg (fun x _ ↦ (g x).2) x),
      Complex.real_smul, mul_comm]

/- English proof (translation)
Use `set U := adeleAtS S ⁻¹' intS S with hUdef`. Establish `hUm : MeasurableSet U` using `measurable_adeleAtS S (measurableSet_intS S)`. Establish `key : ∀ p : ℂ → ℝ, Measurable p → (∀ z, |p z| ≤ ‖z‖) → Integrable (U.indicator fun x ↦ (((p (G x)).toNNReal : ℝ))) (finiteAdeleMeasure K) ∧ Integrable (fun x ↦ F (adeleAtS S x) * (((p (G x)).toNNReal : ℝ) : ℂ)) (finiteAdeleMeasure K) ∧ ∫ x, F (adeleAtS S x) * (((p (G x)).toNNReal …`. Introduce `p hp hpz`. Establish `hgm : Measurable fun x ↦ (p (G x)).toNNReal` using `(hp.comp hGm).real_toNNReal`.

Establish `hinv : ∀ a x, (p (G (adeleSingleS S a + x))).toNNReal = (p (G x)).toNNReal` using `fun a x ↦ by rw [apply_adeleSingleS_add S hG a x]`. Establish `hgi : Integrable (U.indicator fun x ↦ (((p (G x)).toNNReal : ℝ))) (finiteAdeleMeasure K)`. Use `hGi.norm.mono' ((measurable_coe_nnreal_real.comp hgm).indicator hUm).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only [Set.indicator_apply]`. Use `split_ifs`.

Rewrite using `[Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.coe_toNNReal']`. Conclude with `max_le ((le_abs_self _).trans (hpz _)) (norm_nonneg _)`. Simplify using the standard rewrite rules. Take `⟨h1, h2⟩` from `integral_comp_adeleAtS_mul_nnreal hgm hinv hgi hF`. Conclude with `⟨hgi, h1, h2⟩`.

Take `⟨i1, j1, e1⟩` from `key (fun z ↦ z.re) Complex.measurable_re fun z ↦ Complex.abs_re_le_norm z`. Take `⟨i2, j2, e2⟩` from `key (fun z ↦ -z.re) Complex.measurable_re.neg fun z ↦ by`. Rewrite using `[abs_neg]`. Conclude with `Complex.abs_re_le_norm z`. Take `⟨i3, j3, e3⟩` from `key (fun z ↦ z.im) Complex.measurable_im fun z ↦ Complex.abs_im_le_norm z`.

Take `⟨i4, j4, e4⟩` from `key (fun z ↦ -z.im) Complex.measurable_im.neg fun z ↦ by`. Rewrite using `[abs_neg]`. Conclude with `Complex.abs_im_le_norm z`. Establish `hsplit : ∀ z : ℂ, z = ((((z.re).toNNReal : ℝ) - ((-z.re).toNNReal : ℝ) : ℝ) : ℂ) + ((((z.im).toNNReal : ℝ) - ((-z.im).toNNReal : ℝ) : ℝ) : ℂ) * Complex.I` using `fun z ↦ by`. Simplify using `only [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]`.

Conclude with `(Complex.re_add_im z).symm`. Establish `hL : ∀ x, F (adeleAtS S x) * G x = (F (adeleAtS S x) * ((((G x).re).toNNReal : ℝ) : ℂ) - F (adeleAtS S x) * (((-(G x).re).toNNReal : ℝ) : ℂ)) + (F (adeleAtS S x) * ((((G x).im).toNNReal : ℝ) : ℂ) - F (adeleAtS S x) * (((-(G x).im).toNNReal : ℝ) : ℂ)) * Complex.I` using `fun x ↦ by conv_lhs => rw [hsplit (G x)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : ∀ x, U.indicator G x = (((U.indicator (fun x ↦ (((G x).re).toNNReal : ℝ)) x - U.indicator (fun x ↦ ((-(G x).re).toNNReal : ℝ)) x : ℝ) : ℂ)) + (((U.indicator (fun x ↦ (((G x).im).toNNReal : ℝ)) x - U.indicator (fun x ↦ ((-(G x).im).toNNReal : ℝ)) x : ℝ) : ℂ)) * Complex.I` using `fun x ↦ by classical`.

Simplify using `only [Set.indicator_apply]`. Use `split_ifs`. Conclude with `hsplit (G x)`. Simplify using the standard rewrite rules. Use `set f1 := fun x ↦ F (adeleAtS S x) * ((((G x).re).toNNReal : ℝ) : ℂ)`.

Use `set f2 := fun x ↦ F (adeleAtS S x) * (((-(G x).re).toNNReal : ℝ) : ℂ)`. Use `set f3 := fun x ↦ F (adeleAtS S x) * ((((G x).im).toNNReal : ℝ) : ℂ)`. Use `set f4 := fun x ↦ F (adeleAtS S x) * (((-(G x).im).toNNReal : ℝ) : ℂ)`. Use `set r1 := U.indicator (fun x ↦ (((G x).re).toNNReal : ℝ))`. Use `set r2 := U.indicator (fun x ↦ ((-(G x).re).toNNReal : ℝ))`.

Use `set r3 := U.indicator (fun x ↦ (((G x).im).toNNReal : ℝ))`. Use `set r4 := U.indicator (fun x ↦ ((-(G x).im).toNNReal : ℝ))`. Establish `k12 : Integrable (fun x ↦ f1 x - f2 x) (finiteAdeleMeasure K)` using `j1.sub j2`. Establish `k34 : Integrable (fun x ↦ (f3 x - f4 x) * Complex.I) (finiteAdeleMeasure K)` using `(j3.sub j4).mul_const _`. Establish `l12 : Integrable (fun x ↦ ((r1 x - r2 x : ℝ) : ℂ)) (finiteAdeleMeasure K)` using `(i1.sub i2).ofReal`.

Establish `l34 : Integrable (fun x ↦ ((r3 x - r4 x : ℝ) : ℂ) * Complex.I) (finiteAdeleMeasure K)` using `(i3.sub i4).ofReal.mul_const _`. Establish `hL' : (fun x ↦ F (adeleAtS S x) * G x) = fun x ↦ (f1 x - f2 x) + (f3 x - f4 x) * Complex.I`. Use function extensionality and compare the values at `hL`. Establish `hR' : U.indicator G = fun x ↦ ((r1 x - r2 x : ℝ) : ℂ) + ((r3 x - r4 x : ℝ) : ℂ) * Complex.I`. Use function extensionality and compare the values at `hR`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hL']`. Conclude with `k12.add k34`. Rewrite using `[hL', hR', integral_add k12 k34, integral_add l12 l34, integral_sub j1 j2, integral_mul_const, integral_sub j3 j4, e1, e2, e3, e4, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, integral_sub i1 i2, integral_sub i3 i4]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_finiteAdele_local_mul {F : ((v : S) → v.1.adicCompletion K) → ℂ}
    (hF : Integrable F (haarS S)) {G : FiniteAdeleRing (𝓞 K) K → ℂ} (hGm : Measurable G)
    (hG : ∀ x x', (∀ w ∉ S, x w = x' w) → G x = G x')
    (hGi : Integrable ((adeleAtS S ⁻¹' intS S).indicator G) (finiteAdeleMeasure K)) :
    Integrable (fun x ↦ F (adeleAtS S x) * G x) (finiteAdeleMeasure K) ∧
      ∫ x, F (adeleAtS S x) * G x ∂finiteAdeleMeasure K =
        (∫ a, F a ∂haarS S) *
          ∫ x, (adeleAtS S ⁻¹' intS S).indicator G x ∂finiteAdeleMeasure K := by
  set U := adeleAtS S ⁻¹' intS S with hUdef
  have hUm : MeasurableSet U := measurable_adeleAtS S (measurableSet_intS S)
  have key : ∀ p : ℂ → ℝ, Measurable p → (∀ z, |p z| ≤ ‖z‖) →
      Integrable (U.indicator fun x ↦ (((p (G x)).toNNReal : ℝ))) (finiteAdeleMeasure K) ∧
      Integrable (fun x ↦ F (adeleAtS S x) * (((p (G x)).toNNReal : ℝ) : ℂ)) (finiteAdeleMeasure K) ∧
      ∫ x, F (adeleAtS S x) * (((p (G x)).toNNReal : ℝ) : ℂ) ∂finiteAdeleMeasure K =
        (∫ a, F a ∂haarS S) *
          ((∫ x, U.indicator (fun x ↦ (((p (G x)).toNNReal : ℝ))) x ∂finiteAdeleMeasure K : ℝ) : ℂ) := by
    intro p hp hpz
    have hgm : Measurable fun x ↦ (p (G x)).toNNReal := (hp.comp hGm).real_toNNReal
    have hinv : ∀ a x, (p (G (adeleSingleS S a + x))).toNNReal = (p (G x)).toNNReal :=
      fun a x ↦ by rw [apply_adeleSingleS_add S hG a x]
    have hgi : Integrable (U.indicator fun x ↦ (((p (G x)).toNNReal : ℝ))) (finiteAdeleMeasure K) := by
      refine hGi.norm.mono' ((measurable_coe_nnreal_real.comp hgm).indicator hUm).aestronglyMeasurable
        (Eventually.of_forall fun x ↦ ?_)
      classical
      simp only [Set.indicator_apply]
      split_ifs
      · rw [Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.coe_toNNReal']
        exact max_le ((le_abs_self _).trans (hpz _)) (norm_nonneg _)
      · simp
    obtain ⟨h1, h2⟩ := integral_comp_adeleAtS_mul_nnreal hgm hinv hgi hF
    exact ⟨hgi, h1, h2⟩
  obtain ⟨i1, j1, e1⟩ := key (fun z ↦ z.re) Complex.measurable_re fun z ↦ Complex.abs_re_le_norm z
  obtain ⟨i2, j2, e2⟩ := key (fun z ↦ -z.re) Complex.measurable_re.neg fun z ↦ by
    rw [abs_neg]; exact Complex.abs_re_le_norm z
  obtain ⟨i3, j3, e3⟩ := key (fun z ↦ z.im) Complex.measurable_im fun z ↦ Complex.abs_im_le_norm z
  obtain ⟨i4, j4, e4⟩ := key (fun z ↦ -z.im) Complex.measurable_im.neg fun z ↦ by
    rw [abs_neg]; exact Complex.abs_im_le_norm z
  have hsplit : ∀ z : ℂ, z = ((((z.re).toNNReal : ℝ) - ((-z.re).toNNReal : ℝ) : ℝ) : ℂ) +
      ((((z.im).toNNReal : ℝ) - ((-z.im).toNNReal : ℝ) : ℝ) : ℂ) * Complex.I := fun z ↦ by
    simp only [Real.coe_toNNReal', max_zero_sub_max_neg_zero_eq_self]
    exact (Complex.re_add_im z).symm
  have hL : ∀ x, F (adeleAtS S x) * G x =
      (F (adeleAtS S x) * ((((G x).re).toNNReal : ℝ) : ℂ) -
        F (adeleAtS S x) * (((-(G x).re).toNNReal : ℝ) : ℂ)) +
      (F (adeleAtS S x) * ((((G x).im).toNNReal : ℝ) : ℂ) -
        F (adeleAtS S x) * (((-(G x).im).toNNReal : ℝ) : ℂ)) * Complex.I := fun x ↦ by
    conv_lhs => rw [hsplit (G x)]
    push_cast
    ring
  have hR : ∀ x, U.indicator G x =
      (((U.indicator (fun x ↦ (((G x).re).toNNReal : ℝ)) x -
        U.indicator (fun x ↦ ((-(G x).re).toNNReal : ℝ)) x : ℝ) : ℂ)) +
      (((U.indicator (fun x ↦ (((G x).im).toNNReal : ℝ)) x -
        U.indicator (fun x ↦ ((-(G x).im).toNNReal : ℝ)) x : ℝ) : ℂ)) * Complex.I := fun x ↦ by
    classical
    simp only [Set.indicator_apply]
    split_ifs
    · exact hsplit (G x)
    · simp
  set f1 := fun x ↦ F (adeleAtS S x) * ((((G x).re).toNNReal : ℝ) : ℂ)
  set f2 := fun x ↦ F (adeleAtS S x) * (((-(G x).re).toNNReal : ℝ) : ℂ)
  set f3 := fun x ↦ F (adeleAtS S x) * ((((G x).im).toNNReal : ℝ) : ℂ)
  set f4 := fun x ↦ F (adeleAtS S x) * (((-(G x).im).toNNReal : ℝ) : ℂ)
  set r1 := U.indicator (fun x ↦ (((G x).re).toNNReal : ℝ))
  set r2 := U.indicator (fun x ↦ ((-(G x).re).toNNReal : ℝ))
  set r3 := U.indicator (fun x ↦ (((G x).im).toNNReal : ℝ))
  set r4 := U.indicator (fun x ↦ ((-(G x).im).toNNReal : ℝ))
  have k12 : Integrable (fun x ↦ f1 x - f2 x) (finiteAdeleMeasure K) := j1.sub j2
  have k34 : Integrable (fun x ↦ (f3 x - f4 x) * Complex.I) (finiteAdeleMeasure K) :=
    (j3.sub j4).mul_const _
  have l12 : Integrable (fun x ↦ ((r1 x - r2 x : ℝ) : ℂ)) (finiteAdeleMeasure K) := (i1.sub i2).ofReal
  have l34 : Integrable (fun x ↦ ((r3 x - r4 x : ℝ) : ℂ) * Complex.I) (finiteAdeleMeasure K) :=
    (i3.sub i4).ofReal.mul_const _
  have hL' : (fun x ↦ F (adeleAtS S x) * G x) = fun x ↦ (f1 x - f2 x) + (f3 x - f4 x) * Complex.I :=
    funext hL
  have hR' : U.indicator G = fun x ↦ ((r1 x - r2 x : ℝ) : ℂ) + ((r3 x - r4 x : ℝ) : ℂ) * Complex.I :=
    funext hR
  refine ⟨?_, ?_⟩
  · rw [hL']
    exact k12.add k34
  · rw [hL', hR', integral_add k12 k34, integral_add l12 l34, integral_sub j1 j2, integral_mul_const,
      integral_sub j3 j4, e1, e2, e3, e4, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal, integral_sub i1 i2, integral_sub i3 i4]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[mem_integralFiniteAdeles]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun v _ ↦ h v.1, fun v _ ↦ h v⟩`. Introduce and unpack `⟨h1, h2⟩ v`.

Distinguish the cases in `hv : v ∈ S`. Conclude with `h1 ⟨v, hv⟩ (Set.mem_univ _)`. Conclude with `h2 v hv`.
-/
theorem mem_integralFiniteAdeles_iff_adeleAtS (x : FiniteAdeleRing (𝓞 K) K) :
    x ∈ integralFiniteAdeles (𝓞 K) K ↔ adeleAtS S x ∈ intS S ∧ x ∈ awayIntegral S := by
  rw [mem_integralFiniteAdeles]
  constructor
  · intro h
    exact ⟨fun v _ ↦ h v.1, fun v _ ↦ h v⟩
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h1 ⟨v, hv⟩ (Set.mem_univ _)
    · exact h2 v hv

/- English proof (translation)
The claim follows from `(isOpen_awayIntegral S).measurableSet`.
-/
theorem isOpen_awayIntegral' (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)) :=
  (isOpen_awayIntegral S).measurableSet

/- English proof (translation)
Use `set G : FiniteAdeleRing (𝓞 K) K → ℂ := (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 with hGdef`. Establish `hGm : Measurable G` using `measurable_const.indicator (isOpen_awayIntegral' S)`. Establish `hG : ∀ x x', (∀ w ∉ S, x w = x' w) → G x = G x'`. Introduce `x x' h`. Establish `hiff : x ∈ awayIntegral S ↔ x' ∈ awayIntegral S` using `forall_congr' fun w ↦ imp_congr_right fun hw ↦ by rw [h w hw]`.

Simplify using `only [hGdef, Set.indicator_apply, SetLike.mem_coe, hiff, Pi.one_apply]`. Establish `hind : (adeleAtS S ⁻¹' intS S).indicator G = (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1`. Use function extensionality and compare the values at `x`. Simplify using `only [hGdef, Set.indicator_apply, Set.mem_preimage, SetLike.mem_coe, mem_integralFiniteAdeles_iff_adeleAtS (S := S) x]`. Apply the tactic sequence `by_cases h1 : adeleAtS S x ∈ intS S <;> by_cases h2 : x ∈ awayIntegral S <;> simp [h1, h2]`.

Establish `hfin : finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ ∞`. Rewrite using `[finiteAdeleMeasure_integralFiniteAdeles]`. Conclude with `ENNReal.coe_ne_top`. Establish `hGi : Integrable ((adeleAtS S ⁻¹' intS S).indicator G) (finiteAdeleMeasure K)`. Rewrite using `[hind]`.

Conclude with `(integrableOn_const (C := (1 : ℂ)) hfin).integrable_indicator isOpen_integralFiniteAdeles.measurableSet`. Take `⟨h1, h2⟩` from `integral_finiteAdele_local_mul hF hGm hG hGi`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hind, integral_indicator isOpen_integralFiniteAdeles.measurableSet]`. Simplify using `only [Pi.one_apply]`.

Rewrite using `[setIntegral_const, measureReal_def, finiteAdeleMeasure_integralFiniteAdeles, ENNReal.coe_toReal, Complex.real_smul, mul_one, mul_comm]`.
-/
theorem integral_finiteAdele_local_awayIntegral {F : ((v : S) → v.1.adicCompletion K) → ℂ}
    (hF : Integrable F (haarS S)) :
    Integrable (fun x ↦ F (adeleAtS S x) *
      (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 x) (finiteAdeleMeasure K) ∧
      ∫ x, F (adeleAtS S x) * (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 x
          ∂finiteAdeleMeasure K =
        (((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) : ℂ) * ∫ a, F a ∂haarS S := by
  set G : FiniteAdeleRing (𝓞 K) K → ℂ :=
    (awayIntegral S : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 with hGdef
  have hGm : Measurable G := measurable_const.indicator (isOpen_awayIntegral' S)
  have hG : ∀ x x', (∀ w ∉ S, x w = x' w) → G x = G x' := by
    intro x x' h
    have hiff : x ∈ awayIntegral S ↔ x' ∈ awayIntegral S :=
      forall_congr' fun w ↦ imp_congr_right fun hw ↦ by rw [h w hw]
    classical
    simp only [hGdef, Set.indicator_apply, SetLike.mem_coe, hiff, Pi.one_apply]
  have hind : (adeleAtS S ⁻¹' intS S).indicator G =
      (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)).indicator 1 := by
    funext x
    classical
    simp only [hGdef, Set.indicator_apply, Set.mem_preimage, SetLike.mem_coe,
      mem_integralFiniteAdeles_iff_adeleAtS (S := S) x]
    by_cases h1 : adeleAtS S x ∈ intS S <;> by_cases h2 : x ∈ awayIntegral S <;> simp [h1, h2]
  have hfin : finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ ∞ := by
    rw [finiteAdeleMeasure_integralFiniteAdeles]
    exact ENNReal.coe_ne_top
  have hGi : Integrable ((adeleAtS S ⁻¹' intS S).indicator G) (finiteAdeleMeasure K) := by
    rw [hind]
    exact (integrableOn_const (C := (1 : ℂ)) hfin).integrable_indicator
      isOpen_integralFiniteAdeles.measurableSet
  obtain ⟨h1, h2⟩ := integral_finiteAdele_local_mul hF hGm hG hGi
  refine ⟨h1, ?_⟩
  rw [h2, hind, integral_indicator isOpen_integralFiniteAdeles.measurableSet]
  simp only [Pi.one_apply]
  rw [setIntegral_const, measureReal_def, finiteAdeleMeasure_integralFiniteAdeles, ENNReal.coe_toReal,
    Complex.real_smul, mul_one, mul_comm]

end Integrals

end

end GroundTheory.Automorphic.GodementSection
