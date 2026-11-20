import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.SchwartzIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl

/- English proof (translation)
The claim follows from `(BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] exact f.le_seminorm ℂ k m x`.
-/
theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x

/- English proof (translation)
The claim follows from `SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by have h := (weightedDeriv k m f).norm_coe_le_norm x rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h`.
-/
theorem seminorm_le_norm_weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℂ k m f ≤ ‖weightedDeriv k m f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k m f).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_add, Pi.add_apply, SchwartzMap.add_apply]
      rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, BoundedContinuousFunction.coe_smul, Pi.smul_apply,
        RingHom.id_apply]
      rw [show ⇑(a • f) = a • ⇑f from rfl,
        iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weightedDerivCLM_apply (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl

section Param

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

/- English proof (translation)
Establish `h` using `((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG`. Use `h.congr fun w => ?_` and prove the remaining obligations. Simplify using `[weightedDerivCLM_apply, weightedDeriv_apply]`.
-/
theorem continuous_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G) (m : ℕ) (y : E) :
    Continuous fun w => iteratedFDeriv ℝ m (G w) y := by
  have h := ((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG
  refine h.congr fun w => ?_
  simp [weightedDerivCLM_apply, weightedDeriv_apply]

/- English proof (translation)
The claim follows from `(hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)`.
-/
theorem integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν :=
  (hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable
    (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Use function extensionality and compare the values at `x`. Simplify using `only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]`. Conclude with `((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm`.

Consider the case `succ m ih`. Use function extensionality and compare the values at `x`. Use `set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ`. Establish `key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y)`. Introduce `f y`.

Rewrite using `[iteratedFDeriv_succ_eq_comp_left]`. Both sides reduce to the same expression. Establish `hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w))` using `fun w => ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)`. Establish `hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y)`. Introduce `w y`.

Rewrite using `[key, LinearIsometryEquiv.apply_symm_apply]`. Establish `hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν) (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w)) Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable) (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => …` and prove the remaining obligations. Repeatedly rewrite using `[hF']`. Conclude with `(Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable`.

Rewrite using `[norm_fderiv_iteratedFDeriv]`. Conclude with `(G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y`. Rewrite using `[key, ih, hd.fderiv]`. Use `Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)` as an intermediate fact. Simplify using `only [LinearIsometryEquiv.coe_toLinearIsometry] at this`.

Rewrite using `[← this]`. Repeatedly rewrite using `[hF', LinearIsometryEquiv.symm_apply_apply]`.
-/
theorem iteratedFDeriv_eq_integral {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) (m : ℕ) :
    iteratedFDeriv ℝ m g = fun x => ∫ w, iteratedFDeriv ℝ m (G w) x ∂ν := by
  induction m with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]
    exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ m ih =>
    funext x
    set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ
    have key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y) := by
      intro f y
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    have hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w)) := fun w =>
      ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
    have hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y) := by
      intro w y
      rw [key, LinearIsometryEquiv.apply_symm_apply]
    have hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν)
        (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w))
        Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable)
        (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => ?_) (hint 0 (m + 1))
        (.of_forall fun w y _ => (hdiff w y).hasFDerivAt)
      · simp_rw [hF']
        exact (Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable
      · rw [norm_fderiv_iteratedFDeriv]
        exact (G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y
    rw [key, ih, hd.fderiv]
    have := Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
    rw [← this]
    simp_rw [hF', LinearIsometryEquiv.symm_apply_apply]

abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)

def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embed_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) (i : s) : embed s f i = weightedDeriv i.1.1 i.1.2 f := rfl

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i => (norm_weightedDeriv_le _ _ f).trans (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f) (fun j _ => apply_nonneg _ _) i.2)`.
-/
theorem norm_embed_le (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) :
    ‖embed s f‖ ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 f :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i =>
    (norm_weightedDeriv_le _ _ f).trans
      (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f)
        (fun j _ => apply_nonneg _ _) i.2)

/- English proof (translation)
The claim follows from `(seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)`.
-/
theorem seminorm_le_norm_embed (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)

/- English proof (translation)
Take `⟨s, C, -, hC⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)`. Establish `hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f` using `fun f => hC f`. Use `set t := insert ((0 : ℕ), (0 : ℕ)) s`. Establish `hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖` using `fun f => (hL f).trans (mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)`. Establish `hinj : Function.Injective (embed (E` using `E) t) := by`.

Use `(injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_` and prove the remaining obligations. Use extensionality with `x`. Establish `h1` using `seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)`. Rewrite `h1` using `[hf, norm_zero]`. Establish `h2` using `(f.norm_le_seminorm ℂ x).trans h1`.

Simplify using `using h2`. Set `Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t` to `(embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)`. Set `e` to `LinearEquiv.ofInjective Φ hinj`. Establish `he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y` using `fun y => by`. Use `congrArg Subtype.val (e.apply_symm_apply y)` as an intermediate fact.

Conclude with `(LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this`. Set `f0 : LinearMap.range Φ →ₗ[ℂ] ℂ` to `(L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap`. Set `f1 : StrongDual ℂ (LinearMap.range Φ)` to `f0.mkContinuous C fun y => by show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖`. Rewrite using `[← he]`. Conclude with `hLt _`.

Take `⟨ℓ, hℓ, -⟩` from `exists_extension_norm_eq (LinearMap.range Φ) f1`. Establish `hLℓ : ∀ f, L f = ℓ (embed t f)`. Introduce `f`. Establish `h1` using `hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩`. Establish `h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `Subtype.ext rfl`. Establish `h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩` using `h1`. Rewrite using `[h3, LinearMap.mkContinuous_apply]`. Use `show L f = L (e.symm _)`.

Rewrite using `[h2]`. Establish `hcont : Continuous fun w => embed t (G w)` using `(embed t).continuous.comp hG`. Use `haveI : SecondCountableTopology W := inferInstance`. Use `haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _`. Establish `hInt : Integrable (fun w => embed t (G w)) ν` using `(integrable_finset_sum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable (.of_forall fun w => norm_embed_le t (G w))`.

Establish `hemb : embed t g = ∫ w, embed t (G w) ∂ν`. Use function extensionality and compare the values at `i`. Use `BoundedContinuousFunction.ext fun x => ?_` and prove the remaining obligations. Establish `h1` using `((BoundedContinuousFunction.evalCLM ℂ x).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, BoundedContinuousFunction.evalCLM_apply] at h1`.

Rewrite using `[← h1]`. Simplify using `only [embed_apply, weightedDeriv_apply]`. Rewrite using `[integral_smul, iteratedFDeriv_eq_integral hG hint hg]`. Rewrite using `[hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]`. Repeatedly rewrite using `[← hLℓ]`.
-/
theorem clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)
  have hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f := fun f => hC f
  set t := insert ((0 : ℕ), (0 : ℕ)) s
  have hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖ := fun f => (hL f).trans (mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi =>
      seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)
  have hinj : Function.Injective (embed (E := E) t) := by
    refine (injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_
    ext x
    have h1 := seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)
    rw [hf, norm_zero] at h1
    have h2 := (f.norm_le_seminorm ℂ x).trans h1
    simpa using h2
  let Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t := (embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)
  let e := LinearEquiv.ofInjective Φ hinj
  have he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y := fun y => by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    exact (LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this
  let f0 : LinearMap.range Φ →ₗ[ℂ] ℂ := (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap
  let f1 : StrongDual ℂ (LinearMap.range Φ) := f0.mkContinuous C fun y => by
    show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖
    rw [← he]
    exact hLt _
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) f1
  have hLℓ : ∀ f, L f = ℓ (embed t f) := by
    intro f
    have h1 := hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩
    have h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩ := h1
    rw [h3, LinearMap.mkContinuous_apply]
    show L f = L (e.symm _)
    rw [h2]
  have hcont : Continuous fun w => embed t (G w) := (embed t).continuous.comp hG
  haveI : SecondCountableTopology W := inferInstance
  haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _
  have hInt : Integrable (fun w => embed t (G w)) ν :=
    (integrable_finset_sum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable
      (.of_forall fun w => norm_embed_le t (G w))
  have hemb : embed t g = ∫ w, embed t (G w) ∂ν := by
    funext i
    refine BoundedContinuousFunction.ext fun x => ?_
    have h1 := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at h1
    rw [← h1]
    simp only [embed_apply, weightedDeriv_apply]
    rw [integral_smul, iteratedFDeriv_eq_integral hG hint hg]
  rw [hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]
  simp_rw [← hLℓ]

end Param

/- English proof (translation)
Introduce `W _ _ _ _ _ ν _ n L G c g hG hc hint hg`. Establish `hG' : Continuous fun w => c w • G w` using `hc.smul hG`. Establish `hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν`. Introduce `k m`. Simplify `hint k m` using `only [map_smul_eq_mul]`.

Establish `hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν`. Introduce `x`. Rewrite using `[hg x]`. Both sides reduce to the same expression. Rewrite using `[clm_apply_eq_integral L hG' hint' hg']`.

Simplify using `only [map_smul, smul_eq_mul]`.
-/
theorem clm_integral_interchange : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ)
    (G : W → Sch (Fin n)) (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  intro W _ _ _ _ _ ν _ n L G c g hG hc hint hg
  have hG' : Continuous fun w => c w • G w := hc.smul hG
  have hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν := by
    intro k m
    simpa only [map_smul_eq_mul] using hint k m
  have hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν := by
    intro x
    rw [hg x]
    rfl
  rw [clm_apply_eq_integral L hG' hint' hg']
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.SchwartzIntegral
