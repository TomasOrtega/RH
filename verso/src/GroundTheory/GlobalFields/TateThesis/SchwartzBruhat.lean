import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure Filter
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap FourierTransform Real Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_mul, mixedTraceForm_apply]`.
-/
theorem infiniteTrace_mul (x y : InfiniteAdeleRing K) :
    infiniteTrace K (x * y) =
      mixedTraceForm K (homeomorphMixedSpace K x) (homeomorphMixedSpace K y) := by
  rw [← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_mul, mixedTraceForm_apply]

/- English proof (translation)
Establish `hxy : x * y = infiniteAdeleInl (x.1 * y.1) + finiteAdeleInr (x.2 * y.2)` using `(infiniteAdeleInl_add_finiteAdeleInr (x * y)).symm`. Establish `hinf : adelicChar K (infiniteAdeleInl (x.1 * y.1)) = 𝐞 (-infiniteTrace K (x.1 * y.1))` using `adelicChar_infinite _`. Rewrite using `[hxy, AddChar.map_add_eq_mul, Circle.coe_mul, hinf, infiniteTrace_mul, finiteAdelicChar_apply]`.
-/
theorem adelicChar_mul_eq (x y : 𝔸[K]) :
    (adelicChar K (x * y) : ℂ) =
      (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K x.1) (homeomorphMixedSpace K y.1)) : ℂ) *
        (finiteAdelicChar K (x.2 * y.2) : ℂ) := by
  have hxy : x * y = infiniteAdeleInl (x.1 * y.1) + finiteAdeleInr (x.2 * y.2) :=
    (infiniteAdeleInl_add_finiteAdeleInr (x * y)).symm
  have hinf : adelicChar K (infiniteAdeleInl (x.1 * y.1)) = 𝐞 (-infiniteTrace K (x.1 * y.1)) :=
    adelicChar_infinite _
  rw [hxy, AddChar.map_add_eq_mul, Circle.coe_mul, hinf, infiniteTrace_mul, finiteAdelicChar_apply]

def schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) : 𝔸[K] → ℂ :=
  fun x ↦ φ (homeomorphMixedSpace K x.1) * g x.2

variable (K) in

def schwartzBruhat : Submodule ℂ (𝔸[K] → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : 𝓢(mixedSpace K, ℂ), ∃ g ∈ finiteSchwartzBruhat K,
    F = schwartzBruhatTensor φ g}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨φ, g, hg, rfl⟩`.
-/
theorem schwartzBruhatTensor_mem (φ : 𝓢(mixedSpace K, ℂ)) {g : 𝔸ᶠ[K] → ℂ}
    (hg : g ∈ finiteSchwartzBruhat K) : schwartzBruhatTensor φ g ∈ schwartzBruhat K :=
  Submodule.subset_span ⟨φ, g, hg, rfl⟩

/- English proof (translation)
The claim follows from `((measurePreserving_measurableEquivMixedSpace K).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr (φ.integrable (μ := selfDualMeasure K))`.
-/
theorem integrable_schwartz_comp (φ : 𝓢(mixedSpace K, ℂ)) :
    Integrable (fun z ↦ φ (homeomorphMixedSpace K z)) (infiniteAdeleMeasure K) :=
  ((measurePreserving_measurableEquivMixedSpace K).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr (φ.integrable (μ := selfDualMeasure K))

/- English proof (translation)
The claim follows from `(integrable_schwartz_comp φ).mul_prod (integrable_of_mem_finiteSchwartzBruhat hg)`.
-/
theorem integrable_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) {g : 𝔸ᶠ[K] → ℂ}
    (hg : g ∈ finiteSchwartzBruhat K) :
    Integrable (schwartzBruhatTensor φ g) (adeleMeasure K) :=
  (integrable_schwartz_comp φ).mul_prod (integrable_of_mem_finiteSchwartzBruhat hg)

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`. Conclude with `integrable_schwartzBruhatTensor φ hg`. Consider the case `zero => exact integrable_zero _ _ _`.

Consider the case `add G H _ _ hG hH => exact hG.add hH`. Consider the case `smul c G _ hG => exact hG.smul c`.
-/
theorem integrable_of_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Integrable F (adeleMeasure K) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact integrable_schwartzBruhatTensor φ hg
  | zero => exact integrable_zero _ _ _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.smul c

variable (K) in

def adelicFourier (F : 𝔸[K] → ℂ) (y : 𝔸[K]) : ℂ :=
  ∫ x, F x * (adelicChar K (x * y) : ℂ) ∂adeleMeasure K

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp (continuous_mul_const y))`.
-/
theorem continuous_adelicChar_mul_const (y : 𝔸[K]) :
    Continuous fun x : 𝔸[K] ↦ (adelicChar K (x * y) : ℂ) :=
  continuous_subtype_val.comp ((continuous_adelicChar (K := K)).comp (continuous_mul_const y))

/- English proof (translation)
The claim follows from `hF.mono (hF.1.mul (continuous_adelicChar_mul_const y).aestronglyMeasurable) (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])`.
-/
theorem integrable_mul_adelicChar {F : 𝔸[K] → ℂ} (hF : Integrable F (adeleMeasure K))
    (y : 𝔸[K]) :
    Integrable (fun x ↦ F x * (adelicChar K (x * y) : ℂ)) (adeleMeasure K) :=
  hF.mono (hF.1.mul (continuous_adelicChar_mul_const y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [adelicFourier, Pi.add_apply, add_mul]`. Conclude with `integral_add (integrable_mul_adelicChar hF y) (integrable_mul_adelicChar hG y)`.
-/
theorem adelicFourier_add {F G : 𝔸[K] → ℂ} (hF : Integrable F (adeleMeasure K))
    (hG : Integrable G (adeleMeasure K)) :
    adelicFourier K (F + G) = adelicFourier K F + adelicFourier K G := by
  funext y
  simp only [adelicFourier, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_adelicChar hF y) (integrable_mul_adelicChar hG y)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [adelicFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `integral_const_mul c _`.
-/
theorem adelicFourier_smul (c : ℂ) (F : 𝔸[K] → ℂ) :
    adelicFourier K (c • F) = c • adelicFourier K F := by
  funext y
  simp only [adelicFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[adelicFourier]`.
-/
theorem adelicFourier_zero : adelicFourier K (0 : 𝔸[K] → ℂ) = 0 := by
  funext y
  simp [adelicFourier]

/- English proof (translation)
Rewrite using `[mixedFourier_apply]`. Establish `h` using `(measurePreserving_measurableEquivMixedSpace K).integral_comp' (fun m ↦ 𝐞 (-mixedTraceForm K m (homeomorphMixedSpace K y)) • φ m)`. Use `Eq.trans ?_ h` and prove the remaining obligations. Use `integral_congr_ae (Eventually.of_forall fun z ↦ ?_)` and prove the remaining obligations. Simplify using `only [measurableEquivMixedSpace_apply, Circle.smul_def, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_infinite_eq_mixedFourier (φ : 𝓢(mixedSpace K, ℂ)) (y : InfiniteAdeleRing K) :
    ∫ z, φ (homeomorphMixedSpace K z) *
        (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K z) (homeomorphMixedSpace K y)) : ℂ)
        ∂infiniteAdeleMeasure K =
      mixedFourier K φ (homeomorphMixedSpace K y) := by
  rw [mixedFourier_apply]
  have h := (measurePreserving_measurableEquivMixedSpace K).integral_comp'
    (fun m ↦ 𝐞 (-mixedTraceForm K m (homeomorphMixedSpace K y)) • φ m)
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  simp only [measurableEquivMixedSpace_apply, Circle.smul_def, smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `h` using `integral_prod_mul (μ := infiniteAdeleMeasure K) (ν := finiteAdeleMeasure K) (fun z ↦ φ (homeomorphMixedSpace K z) * (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K z) (homeomorphMixedSpace K y.1)) : ℂ)) (fun z ↦ g z * (finiteAdelicChar K (z * y.2) : ℂ))`. Rewrite `h` using `[integral_infinite_eq_mixedFourier]`. Rewrite using `[schwartzBruhatTensor, mixedFourierSchwartz_apply, finiteFourier, ← h, adelicFourier]`. Use `integral_congr_ae (Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations.

Simplify using `only [schwartzBruhatTensor, adelicChar_mul_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adelicFourier_schwartzBruhatTensor (φ : 𝓢(mixedSpace K, ℂ)) (g : 𝔸ᶠ[K] → ℂ) :
    adelicFourier K (schwartzBruhatTensor φ g) =
      schwartzBruhatTensor (mixedFourierSchwartz K φ) (finiteFourier K g) := by
  funext y
  have h := integral_prod_mul (μ := infiniteAdeleMeasure K) (ν := finiteAdeleMeasure K)
    (fun z ↦ φ (homeomorphMixedSpace K z) *
      (𝐞 (-mixedTraceForm K (homeomorphMixedSpace K z) (homeomorphMixedSpace K y.1)) : ℂ))
    (fun z ↦ g z * (finiteAdelicChar K (z * y.2) : ℂ))
  rw [integral_infinite_eq_mixedFourier] at h
  rw [schwartzBruhatTensor, mixedFourierSchwartz_apply, finiteFourier, ← h, adelicFourier]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [schwartzBruhatTensor, adelicChar_mul_eq]
  ring

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`. Rewrite using `[adelicFourier_schwartzBruhatTensor]`. Conclude with `schwartzBruhatTensor_mem _ (finiteFourier_mem_finiteSchwartzBruhat hg)`.

Consider the case `zero => rw [adelicFourier_zero]`. Conclude with `zero_mem _`. Consider the case `add G H hG hH ihG ihH`. Rewrite using `[adelicFourier_add (integrable_of_mem_schwartzBruhat hG) (integrable_of_mem_schwartzBruhat hH)]`. Conclude with `add_mem ihG ihH`.

Consider the case `smul c G _ ih`. Rewrite using `[adelicFourier_smul]`. Conclude with `Submodule.smul_mem _ c ih`.
-/
theorem adelicFourier_mem_schwartzBruhat {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    adelicFourier K F ∈ schwartzBruhat K := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier_schwartzBruhatTensor]
    exact schwartzBruhatTensor_mem _ (finiteFourier_mem_finiteSchwartzBruhat hg)
  | zero => rw [adelicFourier_zero]; exact zero_mem _
  | add G H hG hH ihG ihH =>
    rw [adelicFourier_add (integrable_of_mem_schwartzBruhat hG)
      (integrable_of_mem_schwartzBruhat hH)]
    exact add_mem ihG ihH
  | smul c G _ ih =>
    rw [adelicFourier_smul]
    exact Submodule.smul_mem _ c ih

/- English proof (translation)
Rewrite using `[mixedFourier_apply, mixedFourierInv_apply]`. Use `integral_congr_ae (Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only [map_neg, neg_neg, mixedTraceForm_comm K x m]`.
-/
theorem mixedFourier_neg (f : mixedSpace K → ℂ) (m : mixedSpace K) :
    mixedFourier K f (-m) = mixedFourierInv K f m := by
  rw [mixedFourier_apply, mixedFourierInv_apply]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [map_neg, neg_neg, mixedTraceForm_comm K x m]

/- English proof (translation)
Rewrite using `[← neg_neg m, mixedFourier_neg, mixedFourierInv_mixedFourier, neg_neg]`.
-/
theorem mixedFourier_mixedFourier (φ : 𝓢(mixedSpace K, ℂ)) (m : mixedSpace K) :
    mixedFourier K (mixedFourier K φ) m = φ (-m) := by
  rw [← neg_neg m, mixedFourier_neg, mixedFourierInv_mixedFourier, neg_neg]

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`. Rewrite using `[adelicFourier_schwartzBruhatTensor, adelicFourier_schwartzBruhatTensor, finiteFourier_finiteFourier hg]`. Use function extensionality and compare the values at `x`.

Simplify using `only [schwartzBruhatTensor, mixedFourierSchwartz_apply]`. Rewrite using `[mixedFourier_mixedFourier]`. Use `congr 2`. Use `show -homeomorphMixedSpace K x.1 = homeomorphMixedSpace K (-x.1)`. Rewrite using `[homeomorphMixedSpace_apply, homeomorphMixedSpace_apply, map_neg]`.

Consider the case `zero => funext x`. Simplify using `[adelicFourier_zero]`. Consider the case `add G H hG hH ihG ihH`. Rewrite using `[adelicFourier_add (integrable_of_mem_schwartzBruhat hG) (integrable_of_mem_schwartzBruhat hH), adelicFourier_add (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hG)) (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hH)), ihG, ihH]`. Both sides reduce to the same expression.

Consider the case `smul c G _ ih`. Rewrite using `[adelicFourier_smul, adelicFourier_smul, ih]`. Both sides reduce to the same expression.
-/
theorem adelicFourier_adelicFourier {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    adelicFourier K (adelicFourier K F) = fun x ↦ F (-x) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    rw [adelicFourier_schwartzBruhatTensor, adelicFourier_schwartzBruhatTensor,
      finiteFourier_finiteFourier hg]
    funext x
    simp only [schwartzBruhatTensor, mixedFourierSchwartz_apply]
    rw [mixedFourier_mixedFourier]
    congr 2
    show -homeomorphMixedSpace K x.1 = homeomorphMixedSpace K (-x.1)
    rw [homeomorphMixedSpace_apply, homeomorphMixedSpace_apply, map_neg]
  | zero => funext x; simp [adelicFourier_zero]
  | add G H hG hH ihG ihH =>
    rw [adelicFourier_add (integrable_of_mem_schwartzBruhat hG)
        (integrable_of_mem_schwartzBruhat hH),
      adelicFourier_add (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hG))
        (integrable_of_mem_schwartzBruhat (adelicFourier_mem_schwartzBruhat hH)), ihG, ihH]
    rfl
  | smul c G _ ih =>
    rw [adelicFourier_smul, adelicFourier_smul, ih]
    rfl

/- English proof (translation)
Use `set G : 𝔸[K] → ℂ := fun z ↦ F z * (adelicChar K (z * (a⁻¹ • y)) : ℂ)`. Establish `hG : ∀ x, G (a • x) = F (a • x) * (adelicChar K (x * y) : ℂ)`. Introduce `x`. Simplify using `only [G]`. Rewrite using `[Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, Units.mul_inv, one_mul]`.

Establish `hemb : MeasurableEmbedding fun x : 𝔸[K] ↦ a • x` using `(Homeomorph.smul a).toMeasurableEquiv.measurableEmbedding`. Establish `h` using `hemb.integral_map (μ := adeleMeasure K) G`. Rewrite `h` using `[map_smul_adeleMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (IdeleGroup.ideleModule K a).2.le)]`. Rewrite using `[adelicFourier, adelicFourier]`. Simplify using `only [← hG]`.

Rewrite using `[← h, Complex.real_smul, Complex.ofReal_inv]`.
-/
theorem adelicFourier_comp_smul (a : IdeleGroup K) (F : 𝔸[K] → ℂ) (y : 𝔸[K]) :
    adelicFourier K (fun x ↦ F (a • x)) y =
      ((IdeleGroup.ideleModule K a : ℝ)⁻¹ : ℂ) * adelicFourier K F (a⁻¹ • y) := by
  set G : 𝔸[K] → ℂ := fun z ↦ F z * (adelicChar K (z * (a⁻¹ • y)) : ℂ)
  have hG : ∀ x, G (a • x) = F (a • x) * (adelicChar K (x * y) : ℂ) := by
    intro x
    simp only [G]
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, Units.mul_inv,
      one_mul]
  have hemb : MeasurableEmbedding fun x : 𝔸[K] ↦ a • x :=
    (Homeomorph.smul a).toMeasurableEquiv.measurableEmbedding
  have h := hemb.integral_map (μ := adeleMeasure K) G
  rw [map_smul_adeleMeasure, integral_smul_measure, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (IdeleGroup.ideleModule K a).2.le)] at h
  rw [adelicFourier, adelicFourier]
  simp only [← hG]
  rw [← h, Complex.real_smul, Complex.ofReal_inv]

end

end GroundTheory.Global
