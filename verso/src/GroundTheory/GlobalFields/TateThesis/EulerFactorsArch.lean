import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import GroundTheory.GlobalFields.TateThesis.Gaussian
import GroundTheory.GlobalFields.TateThesis.GaussianComplex

open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real

namespace GroundTheory.Global

noncomputable section

section Units

variable {F : Type*} [NormedField F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `he` using `measurableEmbedding_units_val (F := F)`. Rewrite using `[← he.integral_map, unitsMeasure, he.map_comap]`. Establish `hr : Set.range (Units.val : Fˣ → F) = {0}ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]`.

Conclude with `⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩`. Establish `hac : μ.withDensity (fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) ≪ μ` using `withDensity_absolutelyContinuous _ _`. Rewrite using `[hr, Measure.restrict_eq_self_of_ae_mem (s := {0}ᶜ) (compl_mem_ae_iff.2 (hac hμ)), integral_withDensity_eq_integral_toReal_smul (measurable_density_unitsMeasure m) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[ENNReal.toReal_ofReal (by positivity)]`.
-/
theorem integral_unitsMeasure (μ : Measure F) (hμ : μ {0} = 0) (m : ℕ) (g : F → ℂ) :
    ∫ a : Fˣ, g a ∂unitsMeasure μ m = ∫ x, ((‖x‖ ^ m)⁻¹ : ℝ) • g x ∂μ := by
  have he := measurableEmbedding_units_val (F := F)
  rw [← he.integral_map, unitsMeasure, he.map_comap]
  have hr : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  have hac : μ.withDensity (fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹) ≪ μ := withDensity_absolutelyContinuous _ _
  rw [hr, Measure.restrict_eq_self_of_ae_mem (s := {0}ᶜ) (compl_mem_ae_iff.2 (hac hμ)),
    integral_withDensity_eq_integral_toReal_smul (measurable_density_unitsMeasure m)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [ENNReal.toReal_ofReal (by positivity)]

end Units

/- English proof (translation)
Establish `h1 : ((r ^ n : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (pow_pos hr n).ne'`. Establish `h2 : (r : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`. Rewrite using `[cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (pow_pos hr n).le, ← ofReal_log hr.le, Real.log_pow]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 < r) (n : ℕ) (c : ℂ) :
    ((r ^ n : ℝ) : ℂ) ^ c = (r : ℂ) ^ ((n : ℂ) * c) := by
  have h1 : ((r ^ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr n).ne'
  have h2 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (pow_pos hr n).le,
    ← ofReal_log hr.le, Real.log_pow]
  push_cast
  ring_nf

/- English proof (translation)
Break down `lt_or_gt_of_ne hx with h | h` into its components or cases. Rewrite using `[abs_of_neg h, Real.sign_of_neg h]`. Establish `: (x : ℂ) ≠ 0` using `by exact_mod_cast hx`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[abs_of_pos h, Real.sign_of_pos h]`. Establish `: (x : ℂ) ≠ 0` using `by exact_mod_cast hx`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem ofReal_div_abs_eq_sign {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) / ((|x| : ℝ) : ℂ) = (Real.sign x : ℂ) := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h, Real.sign_of_neg h]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
  · rw [abs_of_pos h, Real.sign_of_pos h]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp

section Place

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/- English proof (translation)
Distinguish the cases in `hw : w.IsReal`. Rewrite using `[infinitePlaceMeasure_of_isReal hw, Measure.map_apply (isometryEquivRealOfIsReal hw).symm.continuous.measurable (measurableSet_singleton 0)]`. Use `measure_mono_null (fun x hx ↦ ?_) (measure_singleton (0 : ℝ))` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢`. Rewrite using `[← (isometryEquivRealOfIsReal hw).apply_symm_apply x, hx]`.

Express the relevant statement in the definitionally equal form `ringEquivRealOfIsReal hw 0 = 0`. Conclude with `map_zero _`. Establish `hc` using `not_isReal_iff_isComplex.1 hw`. Rewrite using `[infinitePlaceMeasure_of_isComplex hc, Measure.map_apply (isometryEquivComplexOfIsComplex hc).symm.continuous.measurable (measurableSet_singleton 0), Measure.smul_apply]`. Use `(mul_eq_zero.2 (Or.inr (measure_mono_null (fun x hx ↦ ?_) (measure_singleton (0 : ℂ))))).trans (by rfl)` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢`. Rewrite using `[← (isometryEquivComplexOfIsComplex hc).apply_symm_apply x, hx]`. Express the relevant statement in the definitionally equal form `ringEquivComplexOfIsComplex hc 0 = 0`. Conclude with `map_zero _`.
-/
theorem infinitePlaceMeasure_zero (w : InfinitePlace K) : infinitePlaceMeasure w {0} = 0 := by
  by_cases hw : w.IsReal
  · rw [infinitePlaceMeasure_of_isReal hw, Measure.map_apply
      (isometryEquivRealOfIsReal hw).symm.continuous.measurable (measurableSet_singleton 0)]
    refine measure_mono_null (fun x hx ↦ ?_) (measure_singleton (0 : ℝ))
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← (isometryEquivRealOfIsReal hw).apply_symm_apply x, hx]
    change ringEquivRealOfIsReal hw 0 = 0
    exact map_zero _
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [infinitePlaceMeasure_of_isComplex hc, Measure.map_apply
      (isometryEquivComplexOfIsComplex hc).symm.continuous.measurable (measurableSet_singleton 0),
      Measure.smul_apply]
    refine (mul_eq_zero.2 (Or.inr (measure_mono_null (fun x hx ↦ ?_)
      (measure_singleton (0 : ℂ))))).trans (by rfl)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← (isometryEquivComplexOfIsComplex hc).apply_symm_apply x, hx]
    change ringEquivComplexOfIsComplex hc 0 = 0
    exact map_zero _

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[infinitePlaceUnitsMeasure, integral_unitsMeasure _ (infinitePlaceMeasure_zero w), infinitePlaceMeasure_of_isReal hw]`. Establish `he : MeasurableEmbedding (isometryEquivRealOfIsReal hw).symm` using `(isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding`. Rewrite using `[he.integral_map]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Establish `hn : ‖(isometryEquivRealOfIsReal hw).symm x‖ = |x|`.

Rewrite using `[← Real.norm_eq_abs, ← (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero]`. Express the relevant statement in the definitionally equal form `(ringEquivRealOfIsReal hw).symm 0 = 0`. Conclude with `map_zero _`. Simplify using `only [mult, if_pos hw, pow_one, hn, Complex.real_smul]`. Use `push_cast`.

Rewrite using `[div_eq_inv_mul]`.
-/
theorem integral_infinitePlaceUnitsMeasure_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (g : w.Completion → ℂ) :
    ∫ a : (w.Completion)ˣ, g a ∂infinitePlaceUnitsMeasure w =
      ∫ x : ℝ, g ((isometryEquivRealOfIsReal hw).symm x) / ((|x| : ℝ) : ℂ) := by
  rw [infinitePlaceUnitsMeasure, integral_unitsMeasure _ (infinitePlaceMeasure_zero w),
    infinitePlaceMeasure_of_isReal hw]
  have he : MeasurableEmbedding (isometryEquivRealOfIsReal hw).symm :=
    (isometryEquivRealOfIsReal hw).symm.toHomeomorph.measurableEmbedding
  rw [he.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have hn : ‖(isometryEquivRealOfIsReal hw).symm x‖ = |x| := by
    rw [← Real.norm_eq_abs, ← (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero]
    change (ringEquivRealOfIsReal hw).symm 0 = 0
    exact map_zero _
  simp only [mult, if_pos hw, pow_one, hn, Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[infinitePlaceUnitsMeasure, integral_unitsMeasure _ (infinitePlaceMeasure_zero w), infinitePlaceMeasure_of_isComplex hw]`. Establish `he : MeasurableEmbedding (isometryEquivComplexOfIsComplex hw).symm` using `(isometryEquivComplexOfIsComplex hw).symm.toHomeomorph.measurableEmbedding`. Rewrite using `[he.integral_map]`. Rewrite using `[complexPlaceMeasure]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)` and prove the remaining obligations.

Establish `hn : ‖(isometryEquivComplexOfIsComplex hw).symm z‖ = ‖z‖`. Rewrite using `[← (isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero]`. Express the relevant statement in the definitionally equal form `(ringEquivComplexOfIsComplex hw).symm 0 = 0`. Conclude with `map_zero _`. Simplify using `only [mult, if_neg (not_isReal_iff_isComplex.2 hw), hn, Complex.real_smul]`.

Use `push_cast`. Rewrite using `[div_eq_inv_mul]`.
-/
theorem integral_infinitePlaceUnitsMeasure_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (g : w.Completion → ℂ) :
    ∫ a : (w.Completion)ˣ, g a ∂infinitePlaceUnitsMeasure w =
      ∫ z : ℂ, g ((isometryEquivComplexOfIsComplex hw).symm z) / ((‖z‖ ^ 2 : ℝ) : ℂ)
        ∂complexPlaceMeasure := by
  rw [infinitePlaceUnitsMeasure, integral_unitsMeasure _ (infinitePlaceMeasure_zero w),
    infinitePlaceMeasure_of_isComplex hw]
  have he : MeasurableEmbedding (isometryEquivComplexOfIsComplex hw).symm :=
    (isometryEquivComplexOfIsComplex hw).symm.toHomeomorph.measurableEmbedding
  rw [he.integral_map]
  rw [complexPlaceMeasure]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  have hn : ‖(isometryEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
    rw [← (isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero]
    change (ringEquivComplexOfIsComplex hw).symm 0 = 0
    exact map_zero _
  simp only [mult, if_neg (not_isReal_iff_isComplex.2 hw), hn,
    Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

end Place

def unitsContinuousHom {A B : Type*} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃+* B) (he : Continuous e) : Aˣ →ₜ* Bˣ where
  toMonoidHom := Units.map (e : A →* B)
  continuous_toFun := Units.continuous_iff.2
    ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

/- English proof (translation)
Distinguish the cases in `hw : w.IsReal`. Use `set e := ringEquivRealOfIsReal hw`. Establish `hec : Continuous e.symm` using `(isometryEquivRealOfIsReal hw).symm.continuous`. Use `set ψ : ℝˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)`. Take `⟨⟨a', τ⟩, hp, -⟩` from `existsUnique_realUnits_circle ψ`.

Use `⟨(((a' : ℕ) : ℤ), τ), fun _ ↦ ⟨by positivity, by have := a'.2; omega⟩, fun a ↦ ?_⟩` and prove the remaining obligations. Establish `hx` using `hp (Units.map (e : w.Completion →* ℝ) a)`. Establish `hψ : ψ (Units.map (e : w.Completion →* ℝ) a) = χ.infiniteComponent w a`. Express the relevant statement in the definitionally equal form `χ.infiniteComponent w (Units.map (e.symm : ℝ →* w.Completion) (Units.map (e : w.Completion →* ℝ) a)) = _`. Use `congr 1`.

Use `ext`. Simplify using the standard rewrite rules. Rewrite `hx` using `[hψ]`. Rewrite using `[hx]`. Use `set x : ℝ := e a`.

Establish `hι : extensionEmbedding w (a : w.Completion) = (x : ℂ)` using `(extensionEmbeddingOfIsReal_apply hw _).symm`. Establish `hn : ‖(a : w.Completion)‖ = |x|`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm`. Establish `hx0 : x ≠ 0` using `(map_ne_zero_iff _ e.injective).2 a.ne_zero`.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[hι, hn, mult, if_pos hw, pow_one, zpow_natCast, ofReal_div_abs_eq_sign hx0]`. Establish `hc` using `not_isReal_iff_isComplex.1 hw set e := ringEquivComplexOfIsComplex hc`. Establish `hec : Continuous e.symm` using `(isometryEquivComplexOfIsComplex hc).symm.continuous`. Use `set ψ : ℂˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)`.

Take `⟨⟨m, τ⟩, hp, -⟩` from `existsUnique_complexUnits_circle ψ`. Use `⟨(m, τ / 2), fun h ↦ absurd h hw, fun a ↦ ?_⟩` and prove the remaining obligations. Establish `hx` using `hp (Units.map (e : w.Completion →* ℂ) a)`. Establish `hψ : ψ (Units.map (e : w.Completion →* ℂ) a) = χ.infiniteComponent w a`. Express the relevant statement in the definitionally equal form `χ.infiniteComponent w (Units.map (e.symm : ℂ →* w.Completion) (Units.map (e : w.Completion →* ℂ) a)) = _`.

Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules. Rewrite `hx` using `[hψ]`. Rewrite using `[hx]`.

Establish `hι : (e a : ℂ) = extensionEmbedding w (a : w.Completion)` using `rfl`. Establish `hn : ‖e a‖ = ‖(a : w.Completion)‖` using `(isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _`. Establish `hpos : 0 < ‖(a : w.Completion)‖` using `norm_pos_iff.2 a.ne_zero`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[hn, hι, mult, if_neg hw, ofReal_pow_cpow hpos]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_infiniteParams (w : InfinitePlace K) :
    ∃ p : ℤ × ℝ, (w.IsReal → 0 ≤ p.1 ∧ p.1 < 2) ∧ ∀ a : (w.Completion)ˣ,
      (χ.infiniteComponent w a : ℂ) =
        (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
          ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  by_cases hw : w.IsReal
  · set e := ringEquivRealOfIsReal hw
    have hec : Continuous e.symm := (isometryEquivRealOfIsReal hw).symm.continuous
    set ψ : ℝˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)
    obtain ⟨⟨a', τ⟩, hp, -⟩ := existsUnique_realUnits_circle ψ
    refine ⟨(((a' : ℕ) : ℤ), τ), fun _ ↦ ⟨by positivity, by have := a'.2; omega⟩, fun a ↦ ?_⟩
    have hx := hp (Units.map (e : w.Completion →* ℝ) a)
    have hψ : ψ (Units.map (e : w.Completion →* ℝ) a) = χ.infiniteComponent w a := by
      change χ.infiniteComponent w (Units.map (e.symm : ℝ →* w.Completion)
        (Units.map (e : w.Completion →* ℝ) a)) = _
      congr 1
      ext
      simp
    rw [hψ] at hx
    rw [hx]
    set x : ℝ := e a
    have hι : extensionEmbedding w (a : w.Completion) = (x : ℂ) :=
      (extensionEmbeddingOfIsReal_apply hw _).symm
    have hn : ‖(a : w.Completion)‖ = |x| := by
      rw [← Real.norm_eq_abs]
      exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
    have hx0 : x ≠ 0 := (map_ne_zero_iff _ e.injective).2 a.ne_zero
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [hι, hn, mult, if_pos hw, pow_one, zpow_natCast, ofReal_div_abs_eq_sign hx0]
  · have hc := not_isReal_iff_isComplex.1 hw
    set e := ringEquivComplexOfIsComplex hc
    have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
    set ψ : ℂˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)
    obtain ⟨⟨m, τ⟩, hp, -⟩ := existsUnique_complexUnits_circle ψ
    refine ⟨(m, τ / 2), fun h ↦ absurd h hw, fun a ↦ ?_⟩
    have hx := hp (Units.map (e : w.Completion →* ℂ) a)
    have hψ : ψ (Units.map (e : w.Completion →* ℂ) a) = χ.infiniteComponent w a := by
      change χ.infiniteComponent w (Units.map (e.symm : ℂ →* w.Completion)
        (Units.map (e : w.Completion →* ℂ) a)) = _
      congr 1
      ext
      simp
    rw [hψ] at hx
    rw [hx]
    have hι : (e a : ℂ) = extensionEmbedding w (a : w.Completion) := rfl
    have hn : ‖e a‖ = ‖(a : w.Completion)‖ :=
      (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    have hpos : 0 < ‖(a : w.Completion)‖ := norm_pos_iff.2 a.ne_zero
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [hn, hι, mult, if_neg hw, ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring

def infiniteParams (w : InfinitePlace K) : ℤ × ℝ := (χ.exists_infiniteParams w).choose

def infiniteWeight (w : InfinitePlace K) : ℤ := (χ.infiniteParams w).1

def infiniteTau (w : InfinitePlace K) : ℝ := (χ.infiniteParams w).2

/- English proof (translation)
The claim follows from `(χ.exists_infiniteParams w).choose_spec.1 hw`.
-/
theorem infiniteWeight_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    0 ≤ χ.infiniteWeight w ∧ χ.infiniteWeight w < 2 :=
  (χ.exists_infiniteParams w).choose_spec.1 hw

/- English proof (translation)
The claim follows from `(χ.exists_infiniteParams w).choose_spec.2 a`.
-/
theorem infiniteComponent_eq (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ χ.infiniteWeight w *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) :=
  (χ.exists_infiniteParams w).choose_spec.2 a

end HeckeCharacter

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

def infiniteTest (w : InfinitePlace K) (a : w.Completion) : ℂ :=
  (if 0 < χ.infiniteWeight w then conj (extensionEmbedding w a) else extensionEmbedding w a) ^
      (χ.infiniteWeight w).natAbs * ((Real.exp (-(π * w.mult * ‖a‖ ^ 2)) : ℝ) : ℂ)

open Classical in

def infiniteGamma (w : InfinitePlace K) (s : ℂ) : ℂ :=
  if w.IsReal then Gammaℝ (s + χ.infiniteTau w * I + χ.infiniteWeight w)
  else Gammaℂ (s + χ.infiniteTau w * I + ((χ.infiniteWeight w).natAbs : ℂ) / 2)

omit [NumberField K] in
open Classical in

def infiniteConst (w : InfinitePlace K) : ℂ := if w.IsReal then 1 else π

omit [NumberField K] in
/- English proof (translation)
Unfold `infiniteConst`. Use `split_ifs`. Conclude with `one_ne_zero`. Conclude with `Real.pi_ne_zero` after adjusting the coercions.
-/
theorem infiniteConst_ne_zero (w : InfinitePlace K) : infiniteConst w ≠ 0 := by
  unfold infiniteConst
  split_ifs
  · exact one_ne_zero
  · exact_mod_cast Real.pi_ne_zero

/- English proof (translation)
Use `set h : w.Completion → ℂ := fun x ↦ χ.infiniteTest w x * (extensionEmbedding w x / (‖x‖ : ℂ)) ^ χ.infiniteWeight w * (((‖x‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) * ((‖x‖ ^ w.mult : ℝ) : ℂ) ^ s) with hh`. Establish `hfun : (fun a : (w.Completion)ˣ ↦ χ.infiniteTest w a * χ.infiniteComponent w a * ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s) = fun a : (w.Completion)ˣ ↦ h a`. Use function extensionality and compare the values at `a`. Simplify using `only [h, χ.infiniteComponent_eq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs' : 0 < (s + χ.infiniteTau w * I).re` using `by simpa using hs`. Rewrite using `[hfun]`. Distinguish the cases in `hw : w.IsReal`. Rewrite using `[integral_infinitePlaceUnitsMeasure_of_isReal hw, infiniteConst, infiniteGamma, if_pos hw, if_pos hw, one_mul]`. Take `⟨hm0, hm2⟩` from `χ.infiniteWeight_of_isReal hw`.

Use `set e := isometryEquivRealOfIsReal hw`. Establish `hι : ∀ x : ℝ, extensionEmbedding w (e.symm x) = (x : ℂ)` using `fun x ↦ by`. Rewrite using `[← extensionEmbeddingOfIsReal_apply hw]`. Conclude with `congrArg (fun y : ℝ ↦ (y : ℂ)) (e.apply_symm_apply x)`. Establish `hn : ∀ x : ℝ, ‖e.symm x‖ = |x|` using `fun x ↦ by`.

Rewrite using `[← Real.norm_eq_abs, ← e.symm.isometry.norm_map_of_map_zero]`. Express the relevant statement in the definitionally equal form `(ringEquivRealOfIsReal hw).symm 0 = 0`. Conclude with `map_zero _`. Establish `hmult : (w.mult : ℝ) = 1` using `by rw [mult, if_pos hw, Nat.cast_one]`. Establish `hmult' : w.mult = 1` using `by rw [mult, if_pos hw]`.

Break down `(show χ.infiniteWeight w = 0 ∨ χ.infiniteWeight w = 1 by omega) with h0 | h1` into its components or cases. Rewrite using `[h0, Int.cast_zero, add_zero, ← integral_realGaussian_mul_abs_cpow hs']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`.

Establish `hx' : (0 : ℝ) < |x|` using `abs_pos.2 hx`. Simplify using `only [h, infiniteTest, h0, hn, hmult', pow_one, zpow_zero, mul_one, Int.natAbs_zero, pow_zero, one_mul, realGaussian_eq_ofReal, sq_abs]`. Rewrite using `[← cpow_add _ _ (by exact_mod_cast hx'.ne')]`. Put the polynomial expressions in normal form. Rewrite using `[h1, Int.cast_one, ← integral_realGaussianOdd_mul_sign_mul_abs_cpow (by linarith)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hx' : (0 : ℝ) < |x|` using `abs_pos.2 hx`. Simplify using `only [h, infiniteTest, h1, hι, hn, hmult', pow_one, zpow_one, Int.natAbs_one, if_pos zero_lt_one, conj_ofReal, realGaussianOdd, sq_abs]`.

Rewrite using `[← cpow_add _ _ (by exact_mod_cast hx'.ne'), ofReal_div_abs_eq_sign hx, ofReal_exp]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hc` using `not_isReal_iff_isComplex.1 hw`. Rewrite using `[integral_infinitePlaceUnitsMeasure_of_isComplex hc, infiniteConst, infiniteGamma, if_neg hw, if_neg hw]`.

Use `set e := isometryEquivComplexOfIsComplex hc`. Establish `hι : ∀ z : ℂ, extensionEmbedding w (e.symm z) = z` using `fun z ↦ e.apply_symm_apply z`. Establish `hn : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖` using `fun z ↦ by`. Rewrite using `[← e.symm.isometry.norm_map_of_map_zero]`. Express the relevant statement in the definitionally equal form `(ringEquivComplexOfIsComplex hc).symm 0 = 0`.

Conclude with `map_zero _`. Establish `hmult : (w.mult : ℝ) = 2` using `by rw [mult, if_neg hw, Nat.cast_ofNat]`. Establish `hmult' : w.mult = 2` using `by rw [mult, if_neg hw]`. Establish `hs'' : 0 < (s + χ.infiniteTau w * I).re + ((-χ.infiniteWeight w).natAbs : ℝ) / 2`. Check the signs of the components of the expression.

Establish `key` using `integral_complexGaussian_mul_zpow_mul_cpow (-χ.infiniteWeight w) hs''`. Rewrite `key` using `[Int.natAbs_neg, neg_neg]`. Rewrite using `[← key]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)` and prove the remaining obligations. Distinguish the cases in `hz : z = 0`.

Simplify using `[hz]`. Establish `hz' : (0 : ℝ) < ‖z‖ ^ 2` using `by positivity`. Establish `htest : χ.infiniteTest w (e.symm z) = complexGaussian (-χ.infiniteWeight w) z`. Simplify using `only [infiniteTest, hι, hn, hmult, complexGaussian, Int.natAbs_neg]`. Establish `hexp : ((Real.exp (-(π * 2 * ‖z‖ ^ 2)) : ℝ) : ℂ) = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)`.

Rewrite using `[ofReal_exp]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[hexp]`. Use `congr 1`.

Distinguish the cases in `hm0 : 0 < χ.infiniteWeight w`. Rewrite using `[if_pos hm0, if_neg (by omega)]`. Rewrite using `[if_neg hm0, if_pos (by omega)]`. Simplify using `only [h, htest, hι, hn, hmult']`. Rewrite using `[← cpow_add _ _ (by exact_mod_cast hz'.ne')]`.

Put the polynomial expressions in normal form.
-/
theorem integral_infiniteTest (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (w.Completion)ˣ, χ.infiniteTest w a * χ.infiniteComponent w a *
      ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infinitePlaceUnitsMeasure w =
      infiniteConst w * χ.infiniteGamma w s := by
  set h : w.Completion → ℂ := fun x ↦ χ.infiniteTest w x *
      (extensionEmbedding w x / (‖x‖ : ℂ)) ^ χ.infiniteWeight w *
      (((‖x‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) * ((‖x‖ ^ w.mult : ℝ) : ℂ) ^ s) with hh
  have hfun : (fun a : (w.Completion)ˣ ↦ χ.infiniteTest w a * χ.infiniteComponent w a *
      ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s) = fun a : (w.Completion)ˣ ↦ h a := by
    funext a
    simp only [h, χ.infiniteComponent_eq]
    ring
  have hs' : 0 < (s + χ.infiniteTau w * I).re := by simpa using hs
  rw [hfun]
  by_cases hw : w.IsReal
  · rw [integral_infinitePlaceUnitsMeasure_of_isReal hw, infiniteConst, infiniteGamma, if_pos hw,
      if_pos hw, one_mul]
    obtain ⟨hm0, hm2⟩ := χ.infiniteWeight_of_isReal hw
    set e := isometryEquivRealOfIsReal hw
    have hι : ∀ x : ℝ, extensionEmbedding w (e.symm x) = (x : ℂ) := fun x ↦ by
      rw [← extensionEmbeddingOfIsReal_apply hw]
      exact congrArg (fun y : ℝ ↦ (y : ℂ)) (e.apply_symm_apply x)
    have hn : ∀ x : ℝ, ‖e.symm x‖ = |x| := fun x ↦ by
      rw [← Real.norm_eq_abs, ← e.symm.isometry.norm_map_of_map_zero]
      change (ringEquivRealOfIsReal hw).symm 0 = 0
      exact map_zero _
    have hmult : (w.mult : ℝ) = 1 := by rw [mult, if_pos hw, Nat.cast_one]
    have hmult' : w.mult = 1 := by rw [mult, if_pos hw]
    rcases (show χ.infiniteWeight w = 0 ∨ χ.infiniteWeight w = 1 by omega) with h0 | h1
    · rw [h0, Int.cast_zero, add_zero, ← integral_realGaussian_mul_abs_cpow hs']
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x = 0
      · simp [hx]
      have hx' : (0 : ℝ) < |x| := abs_pos.2 hx
      simp only [h, infiniteTest, h0, hn, hmult', pow_one, zpow_zero, mul_one,
        Int.natAbs_zero, pow_zero, one_mul, realGaussian_eq_ofReal, sq_abs]
      rw [← cpow_add _ _ (by exact_mod_cast hx'.ne')]
      ring_nf
    · rw [h1, Int.cast_one, ← integral_realGaussianOdd_mul_sign_mul_abs_cpow (by linarith)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x = 0
      · simp [hx]
      have hx' : (0 : ℝ) < |x| := abs_pos.2 hx
      simp only [h, infiniteTest, h1, hι, hn, hmult', pow_one, zpow_one,
        Int.natAbs_one, if_pos zero_lt_one, conj_ofReal, realGaussianOdd, sq_abs]
      rw [← cpow_add _ _ (by exact_mod_cast hx'.ne'), ofReal_div_abs_eq_sign hx, ofReal_exp]
      push_cast
      ring_nf
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [integral_infinitePlaceUnitsMeasure_of_isComplex hc, infiniteConst, infiniteGamma, if_neg hw,
      if_neg hw]
    set e := isometryEquivComplexOfIsComplex hc
    have hι : ∀ z : ℂ, extensionEmbedding w (e.symm z) = z := fun z ↦ e.apply_symm_apply z
    have hn : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ := fun z ↦ by
      rw [← e.symm.isometry.norm_map_of_map_zero]
      change (ringEquivComplexOfIsComplex hc).symm 0 = 0
      exact map_zero _
    have hmult : (w.mult : ℝ) = 2 := by rw [mult, if_neg hw, Nat.cast_ofNat]
    have hmult' : w.mult = 2 := by rw [mult, if_neg hw]
    have hs'' : 0 < (s + χ.infiniteTau w * I).re + ((-χ.infiniteWeight w).natAbs : ℝ) / 2 := by
      positivity
    have key := integral_complexGaussian_mul_zpow_mul_cpow (-χ.infiniteWeight w) hs''
    rw [Int.natAbs_neg, neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z = 0
    · simp [hz]
    have hz' : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
    have htest : χ.infiniteTest w (e.symm z) = complexGaussian (-χ.infiniteWeight w) z := by
      simp only [infiniteTest, hι, hn, hmult, complexGaussian, Int.natAbs_neg]
      have hexp : ((Real.exp (-(π * 2 * ‖z‖ ^ 2)) : ℝ) : ℂ) =
          Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
        rw [ofReal_exp]; push_cast; ring_nf
      rw [hexp]
      congr 1
      by_cases hm0 : 0 < χ.infiniteWeight w
      · rw [if_pos hm0, if_neg (by omega)]
      · rw [if_neg hm0, if_pos (by omega)]
    simp only [h, htest, hι, hn, hmult']
    rw [← cpow_add _ _ (by exact_mod_cast hz'.ne')]
    ring_nf

end HeckeCharacter

end

end GroundTheory.Global
