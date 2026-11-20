import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.FiniteAdeleScaling
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace IsDedekindDomain
  MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `h : LinearMap.mulLeft ℝ c = LinearMap.prodMap (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.1 w) ∘ₗ LinearMap.proj w) (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.2 w) ∘ₗ LinearMap.proj w)` using `LinearMap.ext fun _ ↦ rfl`. Rewrite using `[h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun w _ ↦ LinearMap.det_mulLeft _`. Use `Finset.prod_congr rfl fun w _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← Algebra.norm_complex_apply, Algebra.norm_apply]`. Both sides reduce to the same expression.
-/
theorem det_mulLeft_mixedSpace (c : mixedSpace K) :
    LinearMap.det (LinearMap.mulLeft ℝ c) =
      (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  have h : LinearMap.mulLeft ℝ c = LinearMap.prodMap
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.1 w) ∘ₗ LinearMap.proj w)
      (LinearMap.pi fun w ↦ LinearMap.mulLeft ℝ (c.2 w) ∘ₗ LinearMap.proj w) :=
    LinearMap.ext fun _ ↦ rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ LinearMap.det_mulLeft _
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl

/- English proof (translation)
The claim follows from `|LinearMap.det (LinearMap.mulLeft ℝ c)| = mixedEmbedding.norm c := by rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul, Finset.abs_prod, Finset.abs_prod] congr 1 · refine Finset.prod_congr rfl fun w _ ↦ ?_ rw [mult_isReal, pow_one, normAtPlace …`.
-/
theorem abs_det_mulLeft_mixedSpace (c : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ c)| = mixedEmbedding.norm c := by
  rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]

omit [NumberField K] in

/- English proof (translation)
Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Rewrite using `[normAtPlace_apply_of_isReal hw, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Conclude with `(Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _`. Rewrite using `[normAtPlace_apply_of_isComplex hw, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Conclude with `(Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _`.
-/
theorem normAtPlace_homeomorphMixedSpace (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (homeomorphMixedSpace K x) = ‖x w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw, homeomorphMixedSpace_apply,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

/- English proof (translation)
Rewrite using `[mixedEmbedding.norm_apply, InfiniteAdeleRing.norm_def]`. Simplify using `only [normAtPlace_homeomorphMixedSpace]`.
-/
theorem norm_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    mixedEmbedding.norm (homeomorphMixedSpace K x) = ‖x‖ := by
  rw [mixedEmbedding.norm_apply, InfiniteAdeleRing.norm_def]
  simp only [normAtPlace_homeomorphMixedSpace]

omit [NumberField K] in
/- English proof (translation)
Simplify using `only [homeomorphMixedSpace_apply, map_mul]`.
-/
theorem homeomorphMixedSpace_mul (x y : InfiniteAdeleRing K) :
    homeomorphMixedSpace K (x * y) = homeomorphMixedSpace K x * homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_mul]

variable (K) in

/- English proof (translation)
Rewrite using `[infiniteAdeleMeasure, MeasurableEquiv.map_apply]`. Conclude with `congrArg _ ((measurableEquivMixedSpace K).image_eq_preimage_symm E).symm`.
-/
theorem infiniteAdeleMeasure_apply (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K E = selfDualMeasure K (homeomorphMixedSpace K '' E) := by
  rw [infiniteAdeleMeasure, MeasurableEquiv.map_apply]
  exact congrArg _ ((measurableEquivMixedSpace K).image_eq_preimage_symm E).symm

/- English proof (translation)
Rewrite using `[infiniteAdeleMeasure_apply, infiniteAdeleMeasure_apply, ← norm_homeomorphMixedSpace, ← abs_det_mulLeft_mixedSpace, ← addHaar_image_linearMap]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_smul_set, Units.smul_def, smul_eq_mul, LinearMap.mulLeft_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨x, hx, rfl⟩, (homeomorphMixedSpace_mul _ _).symm⟩`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨x, hx, rfl⟩, homeomorphMixedSpace_mul _ _⟩`.
-/
theorem infiniteAdeleMeasure_smul (a : (InfiniteAdeleRing K)ˣ) (E : Set (InfiniteAdeleRing K)) :
    infiniteAdeleMeasure K (a • E) =
      ENNReal.ofReal ‖(a : InfiniteAdeleRing K)‖ * infiniteAdeleMeasure K E := by
  rw [infiniteAdeleMeasure_apply, infiniteAdeleMeasure_apply,
    ← norm_homeomorphMixedSpace, ← abs_det_mulLeft_mixedSpace, ← addHaar_image_linearMap]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_smul_set, Units.smul_def, smul_eq_mul, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (homeomorphMixedSpace_mul _ _).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, homeomorphMixedSpace_mul _ _⟩

/- English proof (translation)
Use extensionality with `S hS`. Rewrite using `[map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul, ← infiniteAdeleMeasure_smul]`. Use `congr 1`. Conclude with `Set.preimage_smul b S`.
-/
theorem map_mul_left_infiniteAdeleMeasure (b : (InfiniteAdeleRing K)ˣ) :
    (infiniteAdeleMeasure K).map (fun y ↦ (b : InfiniteAdeleRing K) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ •
        infiniteAdeleMeasure K := by
  ext S hS
  rw [map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul,
    ← infiniteAdeleMeasure_smul]
  congr 1
  exact Set.preimage_smul b S

/- English proof (translation)
Use extensionality with `S hS`. Rewrite using `[map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul, ← finiteAdeleMeasure_smul]`. Use `congr 1`. Conclude with `Set.preimage_smul b S`.
-/
theorem map_mul_left_finiteAdeleMeasure (b : (𝔸ᶠ[K])ˣ) :
    (finiteAdeleMeasure K).map (fun y ↦ (b : 𝔸ᶠ[K]) * y) =
      ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((b⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞) •
        finiteAdeleMeasure K := by
  ext S hS
  rw [map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply, smul_eq_mul,
    ← finiteAdeleMeasure_smul]
  congr 1
  exact Set.preimage_smul b S

/- English proof (translation)
Use `set S := (finite_mulSupport_nnnorm_units u).toFinset`. Establish `hS : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊) ⊆ S`. Simplify using `[S]`. Establish `hS' : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖) ⊆ S`. Introduce `v hv`.

Apply `hS` to reduce the goal to its premises. Introduce `h`. Apply `hv` to reduce the goal to its premises. Simplify using `using congrArg NNReal.toReal h`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hS, finprod_eq_prod_of_mulSupport_subset _ hS', NNReal.coe_prod]`.

Both sides reduce to the same expression.
-/
theorem coe_finprod_nnnorm (u : (𝔸ᶠ[K])ˣ) :
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(u : 𝔸ᶠ[K]) v‖ := by
  set S := (finite_mulSupport_nnnorm_units u).toFinset
  have hS : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊) ⊆ S := by
    simp [S]
  have hS' : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖) ⊆ S := by
    intro v hv
    apply hS
    intro h
    apply hv
    simpa using congrArg NNReal.toReal h
  rw [finprod_eq_prod_of_mulSupport_subset _ hS, finprod_eq_prod_of_mulSupport_subset _ hS',
    NNReal.coe_prod]
  rfl

/- English proof (translation)
Rewrite using `[← map_prod_map _ _ (continuous_const_mul _).measurable (continuous_const_mul _).measurable, map_mul_left_infiniteAdeleMeasure, map_mul_left_finiteAdeleMeasure, prod_smul_left, prod_smul_right, smul_smul]`.
-/
theorem map_prodMap_mul_left_prod (b : (InfiniteAdeleRing K)ˣ) (c : (𝔸ᶠ[K])ˣ) :
    ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).map
      (Prod.map (fun y ↦ (b : InfiniteAdeleRing K) * y) (fun y ↦ (c : 𝔸ᶠ[K]) * y)) =
      (ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((c⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞)) •
        (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K) := by
  rw [← map_prod_map _ _ (continuous_const_mul _).measurable (continuous_const_mul _).measurable,
    map_mul_left_infiniteAdeleMeasure, map_mul_left_finiteAdeleMeasure, prod_smul_left,
    prod_smul_right, smul_smul]

/- English proof (translation)
Establish `hsplit : (fun x : 𝔸[K] ↦ a • x) = Prod.map (fun y ↦ ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y) (fun y ↦ ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * y)`. Use function extensionality and compare the values at `fun _ ↦ rfl`. Establish `hc : ENNReal.ofReal ‖(((IdeleGroup.toInfinite K a)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ * ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(((IdeleGroup.toFinite K a)⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹`. Establish `hnn : (0 : ℝ) ≤ ‖((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖`. Rewrite using `[InfiniteAdeleRing.norm_def]`.

Conclude with `Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _`. Rewrite using `[← map_inv, ← map_inv, ← ENNReal.ofReal_coe_nnreal, coe_finprod_nnnorm, ← ENNReal.ofReal_mul hnn, ← Positive.coe_inv, ← map_inv, IdeleGroup.ideleModule_apply]`. Both sides reduce to the same expression. Rewrite using `[hsplit, ← hc]`. Conclude with `map_prodMap_mul_left_prod _ _`.
-/
theorem map_smul_adeleMeasure (a : IdeleGroup K) :
    (adeleMeasure K).map (fun x ↦ a • x) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ • adeleMeasure K := by
  have hsplit : (fun x : 𝔸[K] ↦ a • x) = Prod.map
      (fun y ↦ ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y)
      (fun y ↦ ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * y) :=
    funext fun _ ↦ rfl
  have hc : ENNReal.ofReal ‖(((IdeleGroup.toInfinite K a)⁻¹ : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K)‖ * ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖(((IdeleGroup.toFinite K a)⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ := by
    have hnn : (0 : ℝ) ≤ ‖((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K)‖ := by
      rw [InfiniteAdeleRing.norm_def]
      exact Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
    rw [← map_inv, ← map_inv, ← ENNReal.ofReal_coe_nnreal, coe_finprod_nnnorm,
      ← ENNReal.ofReal_mul hnn, ← Positive.coe_inv, ← map_inv,
      IdeleGroup.ideleModule_apply]
    rfl
  rw [hsplit, ← hc]
  exact map_prodMap_mul_left_prod _ _

/- English proof (translation)
Establish `hE : ((adeleMeasure K).map (fun x ↦ a⁻¹ • x)) E = (ENNReal.ofReal ((IdeleGroup.ideleModule K a⁻¹ : ℝ))⁻¹ • adeleMeasure K) E`. Rewrite using `[map_smul_adeleMeasure]`. Establish `hm` using `(Homeomorph.smul a⁻¹).toMeasurableEquiv.map_apply (μ := adeleMeasure K) E`. Rewrite `hm` using `[show ⇑(Homeomorph.smul a⁻¹).toMeasurableEquiv = fun x : 𝔸[K] ↦ a⁻¹ • x from rfl]`. Rewrite `hE` using `[hm, Measure.smul_apply, smul_eq_mul]`.

Establish `h` using `hE`. Rewrite using `[← Set.preimage_smul_inv]`. Use `h using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_inv, Positive.coe_inv, inv_inv]`.
-/
theorem adeleMeasure_smul (a : IdeleGroup K) (E : Set 𝔸[K]) :
    adeleMeasure K (a • E) = ENNReal.ofReal (IdeleGroup.ideleModule K a : ℝ) * adeleMeasure K E := by
  have hE : ((adeleMeasure K).map (fun x ↦ a⁻¹ • x)) E =
      (ENNReal.ofReal ((IdeleGroup.ideleModule K a⁻¹ : ℝ))⁻¹ • adeleMeasure K) E := by
    rw [map_smul_adeleMeasure]
  have hm := (Homeomorph.smul a⁻¹).toMeasurableEquiv.map_apply (μ := adeleMeasure K) E
  rw [show ⇑(Homeomorph.smul a⁻¹).toMeasurableEquiv = fun x : 𝔸[K] ↦ a⁻¹ • x from rfl] at hm
  rw [hm, Measure.smul_apply, smul_eq_mul] at hE
  have h := hE
  rw [← Set.preimage_smul_inv]
  convert h using 2
  rw [map_inv, Positive.coe_inv, inv_inv]

end

end GroundTheory.Global
