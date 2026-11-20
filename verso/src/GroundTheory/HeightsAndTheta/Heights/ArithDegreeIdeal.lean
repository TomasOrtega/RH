import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `: Module.FinitePresentation (𝓞 K) M` using `Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem projective_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M] : Module.Projective (𝓞 K) M := by
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

instance submodule_projective {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (F : Submodule (𝓞 K) E) :
    Module.Projective (𝓞 K) F := by
  have : Module.IsTorsionFree (𝓞 K) F := inferInstance
  exact projective_of_isTorsionFree F

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (I : Ideal (𝓞 K)) : Module.Projective (𝓞 K) I := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (I : Ideal (𝓞 K)) : Module.Finite (𝓞 K) I := inferInstance

section Comap

variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

def fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fibreMap_tmul (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (z : ComplexAt σ) (e : E') :
    fibreMap σ f (z ⊗ₜ e) = z ⊗ₜ f e := rfl

omit [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E'] in

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap f hf`.
-/
theorem fibreMap_injective (σ : K →+* ℂ) {f : E' →ₗ[𝓞 K] E} (hf : Function.Injective f) :
    Function.Injective (fibreMap σ f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul z e => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem conjMap_fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fibreMap σ f x) = fibreMap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

def HermitianMetric.comap (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) : HermitianMetric K E' where
  form σ := coreComap (h.form σ) (fibreMap σ f) (fibreMap_injective σ hf)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, h.form_conj]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HermitianMetric.comap_inner (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x y : Fibre σ E') :
    ((h.comap f hf).form σ).inner x y = (h.form σ).inner (fibreMap σ f x) (fibreMap σ f y) := rfl

end Comap

def HermitianMetric.ideal (I : Ideal (𝓞 K)) : HermitianMetric K I :=
  (HermitianMetric.integers K).comap (Submodule.subtype I) (Submodule.injective_subtype I)

def HermitianBundle.ideal (I : Ideal (𝓞 K)) : HermitianBundle K := ⟨I, HermitianMetric.ideal I⟩

/- English proof (translation)
Take `⟨a, haI, ha⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `hle : Module.finrank (𝓞 K) I ≤ 1`. Use `Submodule.finrank_le I` as an intermediate fact. Rewrite `this` using `[Module.finrank_self]`. Then use the resulting hypothesis. Establish `hge : 1 ≤ Module.finrank (𝓞 K) I`.

Establish `hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ (⟨a, haI⟩ : I))` using `linearIndependent_unique_iff.mpr (by simpa using ha)`. Simplify using `using hli.fintype_card_le_finrank`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : Module.finrank (𝓞 K) I = 1 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hle : Module.finrank (𝓞 K) I ≤ 1 := by
    have := Submodule.finrank_le I
    rwa [Module.finrank_self] at this
  have hge : 1 ≤ Module.finrank (𝓞 K) I := by
    have hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ (⟨a, haI⟩ : I)) :=
      linearIndependent_unique_iff.mpr (by simpa using ha)
    simpa using hli.fintype_card_le_finrank
  omega

/- English proof (translation)
Take `⟨a, haI, ha⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Use `set s : I := ⟨a, haI⟩`. Establish `hs : s ≠ 0` using `by simpa [s] using ha`. Express the relevant statement in the definitionally equal form `arithDegree (HermitianMetric.ideal I) = _`. Rewrite using `[arithDegree_line _ (finrank_ideal hI) hs]`.

Use `set T : Ideal (𝓞 K) := Ideal.span {a}`. Establish `hTI : T ≤ I` using `(Ideal.span_singleton_le_iff_mem I).mpr haI`. Establish `hcard : Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) * Ideal.absNorm I = (Algebra.norm ℤ a).natAbs`. Rewrite using `[← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply, ← Submodule.card_quotient_mul_card_quotient I T hTI]`. Use `congr 1`.

Establish `hker : LinearMap.ker (T.mkQ ∘ₗ I.subtype) = Submodule.span (𝓞 K) {s}`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, T, Ideal.mem_span_singleton', Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`.

Conclude with `⟨c, Subtype.ext hc⟩`. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, congrArg Subtype.val hc⟩`. Establish `hrange : Submodule.map T.mkQ I = LinearMap.range (T.mkQ ∘ₗ I.subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`.

Rewrite using `[← hker, hrange]`. Conclude with `Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv`. Establish `hnorm : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.ideal I) σ s‖ = ‖σ (a : K)‖`. Introduce `σ`. Establish `h1` using `norm_fibreVec_sq (HermitianMetric.ideal I) σ s`.

Rewrite `h1` using `[HermitianMetric.ideal, HermitianMetric.comap_inner]`. Use `erw [HermitianMetric.integers_inner] at h1`. Simplify using `only [Submodule.subtype_apply, s, LinearMap.id_apply, map_one, mul_one] at h1`. Rewrite `h1` using `[mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1`.

Simplify using `only [hnorm, sum_log_norm_embedding a ha]`. Establish `hN : (0 : ℝ) < Ideal.absNorm I`. Conclude with `Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)` after adjusting the coercions. Establish `hc : (Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) : ℝ) = (Algebra.norm ℤ a).natAbs / Ideal.absNorm I`. Rewrite using `[eq_div_iff hN.ne', ← hcard]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, Real.log_div]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha)` after adjusting the coercions.

Conclude with `hN.ne'`.
-/
theorem arithDegree_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (HermitianBundle.ideal I).arithDegree = -Real.log (Ideal.absNorm I) := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set s : I := ⟨a, haI⟩
  have hs : s ≠ 0 := by simpa [s] using ha
  change arithDegree (HermitianMetric.ideal I) = _
  rw [arithDegree_line _ (finrank_ideal hI) hs]

  set T : Ideal (𝓞 K) := Ideal.span {a}
  have hTI : T ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr haI
  have hcard : Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) * Ideal.absNorm I =
      (Algebra.norm ℤ a).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply,
      ← Submodule.card_quotient_mul_card_quotient I T hTI]
    congr 1
    have hker : LinearMap.ker (T.mkQ ∘ₗ I.subtype) = Submodule.span (𝓞 K) {s} := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, T, Ideal.mem_span_singleton',
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, hc⟩; exact ⟨c, congrArg Subtype.val hc⟩
    have hrange : Submodule.map T.mkQ I = LinearMap.range (T.mkQ ∘ₗ I.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hker, hrange]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv

  have hnorm : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.ideal I) σ s‖ = ‖σ (a : K)‖ := by
    intro σ
    have h1 := norm_fibreVec_sq (HermitianMetric.ideal I) σ s
    rw [HermitianMetric.ideal, HermitianMetric.comap_inner] at h1
    erw [HermitianMetric.integers_inner] at h1
    simp only [Submodule.subtype_apply, s, LinearMap.id_apply, map_one, mul_one] at h1
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  simp only [hnorm, sum_log_norm_embedding a ha]
  have hN : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hc : (Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) : ℝ) =
      (Algebra.norm ℤ a).natAbs / Ideal.absNorm I := by
    rw [eq_div_iff hN.ne', ← hcard]
    push_cast; ring
  rw [hc, Real.log_div]
  · ring
  · exact_mod_cast Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha)
  · exact hN.ne'

/- English proof (translation)
Rewrite using `[arithDegree_ideal top_ne_bot, Ideal.absNorm_top, Nat.cast_one, Real.log_one, neg_zero]`.
-/
example : (HermitianBundle.ideal (⊤ : Ideal (𝓞 K))).arithDegree = 0 := by
  rw [arithDegree_ideal top_ne_bot, Ideal.absNorm_top, Nat.cast_one, Real.log_one, neg_zero]

/- English proof (translation)
Establish `hf` using `(HermitianBundle.exists_linearIndependent_rank E F).choose_spec`. Use `set f := (HermitianBundle.exists_linearIndependent_rank E F).choose`. Rewrite using `[arithDegree_eq _ hf (Fintype.card_fin _)]`. Simplify using `only [HermitianBundle.degree, HermitianBundle.degreeWith, degreeWith]`. Use `congr 2`.

Use `Finset.sum_congr rfl fun σ _ ↦ ?_` and prove the remaining obligations. Use `congr 1`. Establish `hG : (gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)) = Matrix.of fun i j ↦ (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier)) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier))`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hD` using `(posSemidef_gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)).det_nonneg`. Rewrite `hD` using `[hG]`. Simplify using `only [GroundTheory.Heights₂.Heights.gramDet, HermitianBundle.gramDet]`. Rewrite using `[hG]`. Use `congrArg Complex.re (Complex.norm_of_nonneg' hD)` as an intermediate fact.

Simplify `this` using `[f]`.
-/
theorem HermitianBundle.degree_eq_arithDegree (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) :
    E.degree F = GroundTheory.Heights₂.Heights.arithDegree (E.metric.comap F.subtype F.injective_subtype) := by
  have hf := (HermitianBundle.exists_linearIndependent_rank E F).choose_spec
  set f := (HermitianBundle.exists_linearIndependent_rank E F).choose
  rw [arithDegree_eq _ hf (Fintype.card_fin _)]
  simp only [HermitianBundle.degree, HermitianBundle.degreeWith, degreeWith]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  congr 1
  have hG : (gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)) =
      Matrix.of fun i j ↦ (E.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier)) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) := by
    ext i j
    rfl
  have hD := (posSemidef_gram ℂ fun i ↦
    fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)).det_nonneg
  rw [hG] at hD
  simp only [GroundTheory.Heights₂.Heights.gramDet, HermitianBundle.gramDet]
  rw [hG]
  have := congrArg Complex.re (Complex.norm_of_nonneg' hD)
  simpa [f] using this

end

end GroundTheory.Heights₂.Heights
