import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import GroundTheory.AutomorphicForms.RealIwasawaIntegration

open MeasureTheory NumberField Set
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction RightCosetSpace GroundTheory.Global

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def splitEquiv (hn : 0 < n) :
    normOneGL K n × {r : ℝ // 0 < r} ≃ᵐ AdelicGLn.AdelicGL K n :=
  (glNormOneSplitting (K := K) hn).symm.toHomeomorph.toMeasurableEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem splitEquiv_apply (hn : 0 < n) (p : normOneGL K n × {r : ℝ // 0 < r}) :
    splitEquiv (K := K) hn p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 :=
  rfl

/- English proof (translation)
The claim follows from `map_mul (glNormOneSplitting (K := K) hn).symm p q`.
-/
theorem splitEquiv_mul (hn : 0 < n) (p q : normOneGL K n × {r : ℝ // 0 < r}) :
    splitEquiv (K := K) hn (p * q) = splitEquiv hn p * splitEquiv hn q :=
  map_mul (glNormOneSplitting (K := K) hn).symm p q

def splitHaar (hn : 0 < n) (μ : Measure (normOneGL K n)) : Measure (AdelicGLn.AdelicGL K n) :=
  Measure.map (splitEquiv (K := K) hn) (μ.prod posRealMeasure)

variable (hn : 0 < n) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

instance isHaarMeasure_splitHaar : (splitHaar (K := K) hn μ).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map (μ.prod posRealMeasure) (glNormOneSplitting (K := K) hn).symm

/- English proof (translation)
The claim follows from `integral_map_equiv (splitEquiv (K := K) hn) H`.
-/
theorem integral_splitHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : AdelicGLn.AdelicGL K n → E) :
    ∫ g, H g ∂splitHaar hn μ =
      ∫ p, H ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ∂(μ.prod posRealMeasure) :=
  integral_map_equiv (splitEquiv (K := K) hn) H

/- English proof (translation)
The claim follows from `integrable_map_equiv (splitEquiv (K := K) hn) H`.
-/
theorem integrable_splitHaar_iff {E : Type*} [NormedAddCommGroup E] (H : AdelicGLn.AdelicGL K n → E) :
    Integrable H (splitHaar hn μ) ↔
      Integrable (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
        H ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2)) (μ.prod posRealMeasure) :=
  integrable_map_equiv (splitEquiv (K := K) hn) H

variable (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]

def centralHaarConst : ℝ≥0 :=
  Measure.haarScalarFactor ν (splitHaar (K := K) hn μ)

/- English proof (translation)
The claim follows from `Measure.haarScalarFactor_pos_of_isHaarMeasure _ _`.
-/
theorem centralHaarConst_pos : 0 < centralHaarConst hn μ ν :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/- English proof (translation)
The claim follows from `Measure.isMulLeftInvariant_eq_smul ν _`.
-/
theorem eq_centralHaarConst_smul : ν = centralHaarConst hn μ ν • splitHaar (K := K) hn μ :=
  Measure.isMulLeftInvariant_eq_smul ν _

/- English proof (translation)
Establish `hH' : Integrable H (splitHaar hn μ)`. Establish `h` using `eq_centralHaarConst_smul hn μ ν`. Rewrite `hH` using `[h]`. Conclude with `(integrable_smul_measure (by simpa using (centralHaarConst_pos hn μ ν).ne') ENNReal.coe_ne_top).1 hH`. Establish `h` using `eq_centralHaarConst_smul hn μ ν`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_smul_nnreal_measure, integral_splitHaar]`. Rewrite `hH'` using `[integrable_splitHaar_iff]`. Rewrite using `[integral_prod_symm _ hH']`. Simplify using `only [centralSection_mul_comm]`.

Both sides reduce to the same expression.
-/
theorem integral_eq_centralHaarConst_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : AdelicGLn.AdelicGL K n → E} (hH : Integrable H ν) :
    ∫ g, H g ∂ν = (centralHaarConst hn μ ν : ℝ) •
      ∫ s, ∫ y, H (centralSection K n s * (y : AdelicGLn.AdelicGL K n)) ∂μ ∂posRealMeasure := by
  have hH' : Integrable H (splitHaar hn μ) := by
    have h := eq_centralHaarConst_smul hn μ ν
    rw [h] at hH
    exact (integrable_smul_measure (by simpa using (centralHaarConst_pos hn μ ν).ne')
      ENNReal.coe_ne_top).1 hH
  have h := eq_centralHaarConst_smul hn μ ν
  calc ∫ g, H g ∂ν = ∫ g, H g ∂(centralHaarConst hn μ ν • splitHaar hn μ) := by
        conv_lhs => rw [h]
    _ = _ := ?_
  rw [integral_smul_nnreal_measure, integral_splitHaar]
  rw [integrable_splitHaar_iff] at hH'
  rw [integral_prod_symm _ hH']
  simp only [centralSection_mul_comm]
  rfl

/- English proof (translation)
Establish `hc : (centralHaarConst hn μ ν : ℝ≥0∞) ≠ 0`. Simplify using `using (centralHaarConst_pos hn μ ν).ne'`. Establish `h` using `eq_centralHaarConst_smul hn μ ν`. Establish `e : Integrable H ν ↔ Integrable H ((centralHaarConst hn μ ν : ℝ≥0∞) • splitHaar hn μ)` using `by conv_lhs => rw [h]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Rewrite using `[integrable_smul_measure hc ENNReal.coe_ne_top, integrable_splitHaar_iff]`. Simplify using `only [centralSection_mul_comm]`.
-/
theorem integrable_iff_prod (hn : 0 < n) {E : Type*} [NormedAddCommGroup E]
    (H : AdelicGLn.AdelicGL K n → E) :
    Integrable H ν ↔ Integrable (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      H (centralSection K n p.2 * (p.1 : AdelicGLn.AdelicGL K n))) (μ.prod posRealMeasure) := by
  have hc : (centralHaarConst hn μ ν : ℝ≥0∞) ≠ 0 := by
    simpa using (centralHaarConst_pos hn μ ν).ne'
  have h := eq_centralHaarConst_smul hn μ ν
  have e : Integrable H ν ↔ Integrable H ((centralHaarConst hn μ ν : ℝ≥0∞) • splitHaar hn μ) := by
    conv_lhs => rw [h]
    rfl
  rw [e]
  rw [integrable_smul_measure hc ENNReal.coe_ne_top, integrable_splitHaar_iff]
  simp only [centralSection_mul_comm]

instance isMulRightInvariant_splitHaar : (splitHaar (K := K) hn μ).IsMulRightInvariant := by
  have := isMulRightInvariant_normOneGL μ
  refine ⟨fun g => ?_⟩
  rw [splitHaar, Measure.map_map (measurable_mul_const g) (splitEquiv (K := K) hn).measurable]
  have he : (fun x => x * g) ∘ (splitEquiv (K := K) hn) =
      (splitEquiv (K := K) hn) ∘ (fun p => p * (splitEquiv (K := K) hn).symm g) := by
    funext p
    simp only [Function.comp_apply]
    rw [splitEquiv_mul, MeasurableEquiv.apply_symm_apply]
  rw [he, ← Measure.map_map (splitEquiv (K := K) hn).measurable (measurable_mul_const _),
    map_mul_right_eq_self]

/- English proof (translation)
Use `set μ₀ : Measure (normOneGL K n) := Measure.haar`. Establish `h` using `eq_centralHaarConst_smul hn μ₀ ν`. Establish `: ((centralHaarConst hn μ₀ ν) • splitHaar (K` using `K) hn μ₀).IsMulRightInvariant := inferInstance`. Rewrite using `[h]`. Conclude with `this`.
-/
theorem isMulRightInvariant_haar (hn : 0 < n) : ν.IsMulRightInvariant := by
  set μ₀ : Measure (normOneGL K n) := Measure.haar
  have h := eq_centralHaarConst_smul hn μ₀ ν
  have : ((centralHaarConst hn μ₀ ν) • splitHaar (K := K) hn μ₀).IsMulRightInvariant :=
    inferInstance
  rw [h]
  exact this

/- English proof (translation)
Use `isMulRightInvariant_haar ν hn` as an intermediate fact. Conclude with `isInvInvariant_of_isMulRightInvariant ν`.
-/
theorem isInvInvariant_haar (hn : 0 < n) : ν.IsInvInvariant := by
  have := isMulRightInvariant_haar ν hn
  exact isInvInvariant_of_isMulRightInvariant ν

/- English proof (translation)
Use `isInvInvariant_haar ν hn` as an intermediate fact. Conclude with `integral_inv_eq_self H ν`.
-/
theorem integral_comp_inv (hn : 0 < n) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : AdelicGLn.AdelicGL K n → E) : ∫ g, H g⁻¹ ∂ν = ∫ g, H g ∂ν := by
  have := isInvInvariant_haar ν hn
  exact integral_inv_eq_self H ν

end GJGlobal

end

end GroundTheory.Automorphic
