import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.OneVec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Transport

variable {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]

/- English proof (translation)
Take `⟨hH, hF⟩` from `h`. Use `set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm`. Establish `hmap : ν.map e = ν.map m` using `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `ContinuousAddEquiv.isAddHaarMeasure_map ν e`.

Introduce `Φ hc hs hI z`. Rewrite `hI`, the goal using `[hmap]`. Establish `hinner : ∀ t : X, ∫ x, Φ x * χ' x (e t) ∂(ν.map m) = ∫ s, Φ (e s) * χ s t ∂ν`. Introduce `t`. Rewrite using `[integral_map_equiv]`.

Use `integral_congr_ae (ae_of_all _ fun s => ?_)` and prove the remaining obligations. Use `show Φ (e s) * χ' (e s) (e t) = Φ (e s) * χ s t`. Rewrite using `[hχ]`. Establish `hIΨ : Integrable (fun t => ∫ s, Φ (e s) * χ s t ∂ν) ν`. Establish `h0` using `(integrable_map_equiv m _).mp hI`.

Conclude with `h0.congr (ae_of_all _ fun t => hinner t)`. Establish `key` using `hF (fun s => Φ (e s)) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hIΨ (e.symm z)`. Rewrite using `[integral_map_equiv]`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations.

Use `show (∫ x, Φ x * χ' x (e t) ∂(ν.map m)) * χ' (e t) z = (∫ s, Φ (e s) * χ s t ∂ν) * χ t (e.symm z)`. Rewrite using `[hinner t, ← hχ t (e.symm z), e.apply_symm_apply]`. Use `_ = Φ (-z) := by rw [key, map_neg, e.apply_symm_apply]`.
-/
theorem selfDual_map (e : X ≃ₜ+ Y) {ν : Measure X} {χ : X → X → ℂ} {χ' : Y → Y → ℂ}
    (hχ : ∀ s t, χ' (e s) (e t) = χ s t) (h : SelfDual ν χ) : SelfDual (ν.map e) χ' := by
  obtain ⟨hH, hF⟩ := h
  set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm
  have hmap : ν.map e = ν.map m := rfl
  refine ⟨?_, ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν e
  intro Φ hc hs hI z
  rw [hmap] at hI ⊢
  have hinner : ∀ t : X, ∫ x, Φ x * χ' x (e t) ∂(ν.map m) = ∫ s, Φ (e s) * χ s t ∂ν := by
    intro t
    rw [integral_map_equiv]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show Φ (e s) * χ' (e s) (e t) = Φ (e s) * χ s t
    rw [hχ]
  have hIΨ : Integrable (fun t => ∫ s, Φ (e s) * χ s t ∂ν) ν := by
    have h0 := (integrable_map_equiv m _).mp hI
    exact h0.congr (ae_of_all _ fun t => hinner t)
  have key := hF (fun s => Φ (e s)) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hIΨ (e.symm z)
  rw [integral_map_equiv]
  calc ∫ t, (∫ x, Φ x * χ' x (m t) ∂(ν.map m)) * χ' (m t) z ∂ν
      = ∫ t, (∫ s, Φ (e s) * χ s t ∂ν) * χ t (e.symm z) ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        show (∫ x, Φ x * χ' x (e t) ∂(ν.map m)) * χ' (e t) z =
          (∫ s, Φ (e s) * χ s t ∂ν) * χ t (e.symm z)
        rw [hinner t, ← hχ t (e.symm z), e.apply_symm_apply]
    _ = Φ (-z) := by rw [key, map_neg, e.apply_symm_apply]

omit [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] in

/- English proof (translation)
Take `⟨hg, hS⟩` from `h`. Use `set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm`. Use `⟨hg.comp e.continuous.continuousOn (fun s hs => hB s hs), fun S hSc hSB => ?_⟩` and prove the remaining obligations. Establish `h1` using `hS (e '' S) (hSc.image e.continuous) (by rintro _ ⟨s, hs, rfl⟩; exact hB s (hSB hs))`. Establish `hpre : f ⁻¹' (ι '' (e '' S)) = f' ⁻¹' (id '' S)`.

Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨s, hs, rfl⟩, hy⟩`. Rewrite `hy` using `[hf v]`. Establish `hs' : s = f' v` using `EquivLike.injective e (hι hy)`.

Conclude with `⟨f' v, hs' ▸ hs, rfl⟩`. Introduce and unpack `⟨s, hs, hsv⟩`. Conclude with `⟨e s, ⟨s, hs, rfl⟩, by rw [hf v, ← hsv]; rfl⟩`. Rewrite `h1` using `[hpre]`. Rewrite using `[h1]`.

Establish `hmap : ν.map e = ν.map m` using `rfl`. Rewrite using `[hmap, setIntegral_map_equiv]`. Rewrite using `[show ⇑m ⁻¹' (⇑e '' S) = S from Set.preimage_image_eq S (EquivLike.injective e)]`. Both sides reduce to the same expression.
-/
theorem density_comp {V Z : Type} [MeasurableSpace V] (e : X ≃ₜ+ Y) {μ : Measure V} {ν : Measure X}
    {f : V → Z} {ι : Y → Z} (hι : Function.Injective ι) {f' : V → X} (hf : ∀ v, f v = ι (e (f' v)))
    {B' : Set Y} {B : Set X} (hB : ∀ s ∈ B, e s ∈ B') {Φ : V → ℂ} {g : Y → ℂ}
    (h : IsContDensityOn μ f ι (ν.map e) B' Φ g) : IsContDensityOn μ f' id ν B Φ (fun s => g (e s)) := by
  obtain ⟨hg, hS⟩ := h
  set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm
  refine ⟨hg.comp e.continuous.continuousOn (fun s hs => hB s hs), fun S hSc hSB => ?_⟩
  have h1 := hS (e '' S) (hSc.image e.continuous) (by rintro _ ⟨s, hs, rfl⟩; exact hB s (hSB hs))
  have hpre : f ⁻¹' (ι '' (e '' S)) = f' ⁻¹' (id '' S) := by
    ext v
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, hy⟩
      rw [hf v] at hy
      have hs' : s = f' v := EquivLike.injective e (hι hy)
      exact ⟨f' v, hs' ▸ hs, rfl⟩
    · rintro ⟨s, hs, hsv⟩
      exact ⟨e s, ⟨s, hs, rfl⟩, by rw [hf v, ← hsv]; rfl⟩
  rw [hpre] at h1
  rw [h1]
  have hmap : ν.map e = ν.map m := rfl
  rw [hmap, setIntegral_map_equiv]
  rw [show ⇑m ⁻¹' (⇑e '' S) = S from Set.preimage_image_eq S (EquivLike.injective e)]
  rfl

end Transport

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 τ, h.2.2.2 τ, star_star]`.
-/
theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hc` using `h.2.1.isComplex w`. Rewrite `hc` using `[InfinitePlace.isComplex_iff]`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h.2.2.2, hno]`.
-/
private theorem exists_not_fixed_of_isCMExt (h : IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  by_contra hno
  push Not at hno
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := h.2.1.isComplex w
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h.2.2.2, hno]

/- English proof (translation)
Take `⟨y, hy⟩` from `exists_not_fixed_of_isCMExt h`. Use `⟨y - σ y, by rw [map_sub, sigma_sigma h]; ring, ?_⟩` and prove the remaining obligations. Establish `hw : y - σ y ≠ 0` using `sub_ne_zero.mpr (Ne.symm hy)`. Establish `hli : LinearIndependent F ![(1 : E), y - σ y]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `h2` using `congrArg σ hst`. Simplify using `only [map_add, map_mul, AlgHom.commutes, map_sub, sigma_sigma h, map_zero] at h2`. Establish `h3 : (2 : E) * algebraMap F E t * (y - σ y) = 0` using `by linear_combination hst - h2`.

Establish `ht : algebraMap F E t = 0`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Break down `mul_eq_zero.mp h4 with h5 | h5` into its components or cases. Conclude with `absurd h5 two_ne_zero`. Conclude with `h5`.

Conclude with `absurd h4 hw`. Establish `ht' : t = 0` using `(algebraMap F E).injective (by rw [ht, map_zero])`. Substitute `ht'` using the available equality. Use `⟨(algebraMap F E).injective ?_, rfl⟩` and prove the remaining obligations. Simplify using `using hst`.

Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h.2.2.1])`. Introduce `x`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).mp (hsp ▸ Submodule.mem_top : x ∈ _)`. Use `⟨c 0, c 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Fin.sum_univ_two]`.

Simplify using `[Algebra.smul_def]`.
-/
private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (h : IsCMExt F E σ) :
    ∃ w : E, σ w = -w ∧ ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * w := by
  obtain ⟨y, hy⟩ := exists_not_fixed_of_isCMExt h
  refine ⟨y - σ y, by rw [map_sub, sigma_sigma h]; ring, ?_⟩
  have hw : y - σ y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hli : LinearIndependent F ![(1 : E), y - σ y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    simp only [map_add, map_mul, AlgHom.commutes, map_sub, sigma_sigma h, map_zero] at h2
    have h3 : (2 : E) * algebraMap F E t * (y - σ y) = 0 := by linear_combination hst - h2
    have ht : algebraMap F E t = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd h5 two_ne_zero
        · exact h5
      · exact absurd h4 hw
    have ht' : t = 0 := (algebraMap F E).injective (by rw [ht, map_zero])
    subst ht'
    refine ⟨(algebraMap F E).injective ?_, rfl⟩
    simpa using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h.2.2.1])
  intro x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hsp ▸ Submodule.mem_top : x ∈ _)
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

/- English proof (translation)
Take `⟨w, hw, hdec⟩` from `exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul h`. Establish `htw : Algebra.trace F E w = 0`. Set `σe : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun z => sigma_sigma h z) (AlgHom.ext fun z => sigma_sigma h z)`. Establish `h1` using `Algebra.trace_eq_of_algEquiv σe w`. Express the relevant statement in the definitionally equal form `Algebra.trace F E (σ w) = _ at h1`.

Rewrite `h1` using `[hw, map_neg]`. Establish `h2 : (2 : F) * Algebra.trace F E w = 0` using `by linear_combination -h1`. Simplify using `using h2`. Take `⟨a, b, rfl⟩` from `hdec x`. Establish `e1 : σ (algebraMap F E a + algebraMap F E b * w) = algebraMap F E a - algebraMap F E b * w`.

Rewrite using `[map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Algebra.trace F E (algebraMap F E a + algebraMap F E b * w) = 2 * a`. Rewrite using `[map_add, ← Algebra.smul_def, map_smul, htw, smul_zero, add_zero, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]`. Rewrite using `[e1, e2, map_mul, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_sigma (h : IsCMExt F E σ) (x : E) : x + σ x = algebraMap F E (Algebra.trace F E x) := by
  obtain ⟨w, hw, hdec⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul h
  have htw : Algebra.trace F E w = 0 := by
    let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun z => sigma_sigma h z)
      (AlgHom.ext fun z => sigma_sigma h z)
    have h1 := Algebra.trace_eq_of_algEquiv σe w
    change Algebra.trace F E (σ w) = _ at h1
    rw [hw, map_neg] at h1
    have h2 : (2 : F) * Algebra.trace F E w = 0 := by linear_combination -h1
    simpa using h2
  obtain ⟨a, b, rfl⟩ := hdec x
  have e1 : σ (algebraMap F E a + algebraMap F E b * w) = algebraMap F E a - algebraMap F E b * w := by
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hw]
    ring
  have e2 : Algebra.trace F E (algebraMap F E a + algebraMap F E b * w) = 2 * a := by
    rw [map_add, ← Algebra.smul_def, map_smul, htw, smul_zero, add_zero, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul,
      Nat.cast_ofNat]
  rw [e1, e2, map_mul, map_ofNat]
  ring

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Establish `e : r ⊗ₜ[F] x = r • ((1 : R) ⊗ₜ[F] x)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, smul_eq_mul]`. Use `congr 1`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply]`. Establish `hl : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = (Algebra.lmul F E x).baseChange R`.

Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => simp [Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.

Rewrite using `[hl, LinearMap.trace_baseChange]`.
-/
theorem trace_tmul (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have e : r ⊗ₜ[F] x = r • ((1 : R) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have hl : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = (Algebra.lmul F E x).baseChange R := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  rw [hl, LinearMap.trace_baseChange]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x`. Rewrite using `[trace_tmul]`. Establish `hs : sigR R σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x` using `by simp [sigR]`.

Rewrite using `[hs, ← TensorProduct.tmul_add, add_sigma h, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, ← hp, ← hq]`. Normalize the expressions using the abelian group laws.
-/
theorem add_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    z + sigR R σ z = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [trace_tmul]
    have hs : sigR R σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x := by simp [sigR]
    rw [hs, ← TensorProduct.tmul_add, add_sigma h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply, Algebra.algebraMap_eq_smul_one (A := E),
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  | add p q hp hq => rw [map_add, map_add, map_add, ← hp, ← hq]; abel

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x => simp [sigR, sigma_sigma h]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.
-/
theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [sigR, sigma_sigma h]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]`. Use `show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (t ⊗ₜ[F] (1 : E)) = t ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]`.
-/
theorem sigR_algebraMap (t : R) : sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (t ⊗ₜ[F] (1 : E)) = t ⊗ₜ[F] (1 : E)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

/- English proof (translation)
Rewrite using `[show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]`. Evaluate the numerical expressions.
-/
theorem half_two : algebraMap F R (1 / 2) * 2 = 1 := by
  rw [show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

/- English proof (translation)
Rewrite using `[map_mul, ← add_sigR R h z, hz]`. Establish `h2` using `congrArg (algebraMap R (R ⊗[F] E)) (half_two (F := F) R)`. Rewrite `h2` using `[map_mul, map_one, map_ofNat]`. Take the linear combination `z * h2`.
-/
theorem fixed_eq (h : IsCMExt F E σ) {z : R ⊗[F] E} (hz : sigR R σ z = z) :
    algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) = z := by
  rw [map_mul, ← add_sigR R h z, hz]
  have h2 := congrArg (algebraMap R (R ⊗[F] E)) (half_two (F := F) R)
  rw [map_mul, map_one, map_ofNat] at h2
  linear_combination z * h2

/- English proof (translation)
Establish `e : algebraMap R (R ⊗[F] E) t = t ⊗ₜ[F] (1 : E)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]`. Rewrite using `[e, trace_tmul, ← map_one (algebraMap F E), Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul, mul_one, Nat.cast_ofNat, map_ofNat]`. Take the linear combination `t * half_two (F := F) R`.
-/
theorem half_trace (h : IsCMExt F E σ) (t : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) t) = t := by
  have e : algebraMap R (R ⊗[F] E) t = t ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [e, trace_tmul, ← map_one (algebraMap F E), Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul,
    mul_one, Nat.cast_ofNat, map_ofNat]
  linear_combination t * half_two (F := F) R

/- English proof (translation)
Establish `hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i`. Introduce `i j`. Simplify using `[JR, inclR, sigR, hJ.1 j i]`. Simplify using `only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h, hJR]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigR_hR (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [JR, inclR, sigR, hJ.1 j i]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h, hJR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def hermOne (h : IsCMExt F E σ) : R ≃ₜ+ HermR R σ 1 where
  toFun t := ⟨fun _ _ => algebraMap R (R ⊗[F] E) t, fun _ _ => sigR_algebraMap R t⟩
  invFun S := algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 0 0)
  left_inv t := half_trace R h t
  right_inv S := by
    apply Subtype.ext
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact fixed_eq R h (S.2 0 0)
  map_add' s t := by
    apply Subtype.ext
    funext a b
    exact map_add _ s t
  continuous_toFun := by
    haveI := isModTop (F := F) (E := E) R
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
    refine Continuous.subtype_mk (continuous_pi fun _ => continuous_pi fun _ => ?_) _
    simp only [Algebra.algebraMap_eq_smul_one]
    fun_prop
  continuous_invFun := by
    haveI := isModTop (F := F) (E := E) R
    refine continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))).comp ?_)
    exact (continuous_apply_apply 0 0).comp continuous_subtype_val

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermOne_val (h : IsCMExt F E σ) (t : R) (a b : Fin 1) :
    (hermOne R h t).1 a b = algebraMap R (R ⊗[F] E) t := rfl

/- English proof (translation)
Simplify using `only [pairHerm, hermOne_val R h, Fin.sum_univ_one, ← map_mul]`. Conclude with `half_trace R h (s * t)`.
-/
theorem pair_hermOne (h : IsCMExt F E σ) (s t : R) : pairHerm R σ 1 (hermOne R h s) (hermOne R h t) = s * t := by
  simp only [pairHerm, hermOne_val R h, Fin.sum_univ_one, ← map_mul]
  exact half_trace R h (s * t)

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[hermOne_val R h, Subsingleton.elim a 0, Subsingleton.elim b 0]`. Conclude with `(fixed_eq R h (sigR_hR R h hJ (X 0))).symm`.
-/
theorem gram_hermOne (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (X : Fin 1 → Fin M → R ⊗[F] E) : gramR R σ J X = (hermOne R h (qR R σ J (X 0))).1 := by
  ext a b
  rw [hermOne_val R h, Subsingleton.elim a 0, Subsingleton.elim b 0]
  exact (fixed_eq R h (sigR_hR R h hJ (X 0))).symm

/- English proof (translation)
Rewrite using `[Matrix.det_fin_one, hermOne_val R h]`. Conclude with `ht.map _`.
-/
theorem unit_hermOne (h : IsCMExt F E σ) {t : R} (ht : IsUnit t) : IsUnit (hermOne R h t).1.det := by
  rw [Matrix.det_fin_one, hermOne_val R h]
  exact ht.map _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a b`. Rewrite using `[hermOne_val R h]`. Use `show inclR R (algebraMap F E β) = _`. Rewrite using `[inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]`.
-/
theorem hermOf_eq (h : IsCMExt F E σ) (β : F) (hT) :
    hermOf R σ (fun _ _ : Fin 1 => algebraMap F E β) hT = hermOne R h (algebraMap F R β) := by
  apply Subtype.ext
  funext a b
  rw [hermOne_val R h]
  show inclR R (algebraMap F E β) = _
  rw [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]

end Field

/- English proof (translation)
Introduce `N`. Establish `: IsModuleTopology (Ainf F) (Ainf F ⊗[F] E)` using `⟨rfl⟩`. Establish `hsize : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ)`. Unfold `sizeTup sizeInf`. Use `continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_` and prove the remaining obligations.

Establish `hk : Continuous fun y : Ainf F ⊗[F] E => (Algebra.TensorProduct.basis (Ainf F) b).repr y k` using `(IsModuleTopology.continuous_of_linearMap (R := Ainf F) ((Algebra.TensorProduct.basis (Ainf F) b).coord k)).congr fun y => Module.Basis.coord_apply _ _ _`. Conclude with `(((continuous_apply v).comp hk).comp ((continuous_apply i).comp (continuous_apply a))).norm`. Establish `hg : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N` using `hc.norm.mul ((continuous_const.add hsize).pow N)`. Take `⟨C, hC⟩` from `hg.bounded_above_of_compact_support hs.norm.mul_right`. Conclude with `⟨C, fun X => (Real.le_norm_self _).trans (hC X)⟩`.
-/
theorem rapid_of_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d M n : ℕ} (b : Module.Basis (Fin d) F E) {Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ}
    (hc : Continuous Φ) (hs : HasCompactSupport Φ) : RapidDecay b Φ := by
  intro N
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hsize : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup sizeInf
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
    have hk : Continuous fun y : Ainf F ⊗[F] E => (Algebra.TensorProduct.basis (Ainf F) b).repr y k :=
      (IsModuleTopology.continuous_of_linearMap (R := Ainf F)
        ((Algebra.TensorProduct.basis (Ainf F) b).coord k)).congr fun y => Module.Basis.coord_apply _ _ _
    exact (((continuous_apply v).comp hk).comp ((continuous_apply i).comp (continuous_apply a))).norm
  have hg : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hc.norm.mul ((continuous_const.add hsize).pow N)
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hs.norm.mul_right
  exact ⟨C, fun X => (Real.le_norm_self _).trans (hC X)⟩

/- English proof (translation)
Establish `: IsModuleTopology R (R ⊗[F] E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (R ⊗[F] E)` using `IsModuleTopology.toContinuousAdd R (R ⊗[F] E)`. Establish `: ContinuousSMul R (R ⊗[F] E)` using `IsModuleTopology.toContinuousSMul R (R ⊗[F] E)`. Establish `: ContinuousNeg (R ⊗[F] E)`. Use `⟨?_⟩` and prove the remaining obligations.

Establish `hn : (fun x : R ⊗[F] E => -x) = fun x => (-1 : R) • x`. Use function extensionality and compare the values at `fun x => (neg_one_smul R x).symm`. Rewrite using `[hn]`. Conclude with `continuous_const_smul _`. Establish `: IsTopologicalAddGroup (R ⊗[F] E)` using `{ toContinuousAdd := inferInstance, toContinuousNeg := inferInstance }`.

Use `infer_instance`.
-/
theorem hermGroup {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (n : ℕ) : IsTopologicalAddGroup (HermR R σ n) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have : ContinuousNeg (R ⊗[F] E) := by
    refine ⟨?_⟩
    have hn : (fun x : R ⊗[F] E => -x) = fun x => (-1 : R) • x :=
      funext fun x => (neg_one_smul R x).symm
    rw [hn]
    exact continuous_const_smul _
  have : IsTopologicalAddGroup (R ⊗[F] E) :=
    { toContinuousAdd := inferInstance, toContinuousNeg := inferInstance }
  infer_instance

section Sd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R]

/- English proof (translation)
Use `hermGroup σ R 1` as an intermediate fact. Establish `: BorelSpace (HermR R σ 1)` using `⟨rfl⟩`. Use `selfDual_map (hermOne R h).symm ?_ hν` and prove the remaining obligations. Introduce `S T`. Take `⟨s, rfl⟩` from `EquivLike.surjective (hermOne R h) S`.

Take `⟨t, rfl⟩` from `EquivLike.surjective (hermOne R h) T`. Use `show ψ ((hermOne R h).symm (hermOne R h s) * (hermOne R h).symm (hermOne R h t)) = ψ (pairHerm R σ 1 (hermOne R h s) (hermOne R h t))`. Rewrite using `[ContinuousAddEquiv.symm_apply_apply, ContinuousAddEquiv.symm_apply_apply, pair_hermOne R h]`.
-/
theorem sd_of_herm (h : IsCMExt F E σ) {ψ : R → ℂ} {ν : Measure (HermR R σ 1)} (hν : SdHerm F E σ R ψ 1 ν) :
    SelfDual (ν.map (hermOne R h).symm) (fun s t => ψ (s * t)) := by
  have := hermGroup σ R 1
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  refine selfDual_map (hermOne R h).symm ?_ hν
  intro S T
  obtain ⟨s, rfl⟩ := EquivLike.surjective (hermOne R h) S
  obtain ⟨t, rfl⟩ := EquivLike.surjective (hermOne R h) T
  show ψ ((hermOne R h).symm (hermOne R h s) * (hermOne R h).symm (hermOne R h t)) =
    ψ (pairHerm R σ 1 (hermOne R h s) (hermOne R h t))
  rw [ContinuousAddEquiv.symm_apply_apply, ContinuousAddEquiv.symm_apply_apply, pair_hermOne R h]

/- English proof (translation)
Use `hermGroup σ R 1` as an intermediate fact. Establish `: BorelSpace (HermR R σ 1)` using `⟨rfl⟩`. Unfold `SdHerm`. Conclude with `selfDual_map (hermOne R h) (χ' := fun S T => ψ (pairHerm R σ 1 S T)) (fun s t => congrArg ψ (pair_hermOne R h s t)) hν`.
-/
theorem sd_to_herm (h : IsCMExt F E σ) {ψ : R → ℂ} {ν : Measure R} (hν : SelfDual ν (fun s t => ψ (s * t))) :
    SdHerm F E σ R ψ 1 (ν.map (hermOne R h)) := by
  have := hermGroup σ R 1
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  unfold SdHerm
  exact selfDual_map (hermOne R h) (χ' := fun S T => ψ (pairHerm R σ 1 S T))
    (fun s t => congrArg ψ (pair_hermOne R h s t)) hν

/- English proof (translation)
Establish `: BorelSpace (HermR R σ 1)` using `⟨rfl⟩`. Establish `key` using `density_comp (V := Fin 1 → Fin M → R ⊗[F] E) (Z := Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) (hermOne R h) (μ := μ) (ν := ν) (f := gramR R σ J) (ι := Subtype.val) Subtype.val_injective (f' := fun X => qR R σ J (X 0)) (fun X => gram_hermOne R h hJ X) (B' := {S | IsUnit (S : Matrix (Fin 1 …`. Conclude with `key hd`.
-/
theorem dens_of_herm (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (Fin 1 → Fin M → R ⊗[F] E)} {ν : Measure R} {B : Set R} (hB : ∀ s ∈ B, IsUnit s)
    {Φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ} {g : HermR R σ 1 → ℂ}
    (hd : IsContDensityOn μ (gramR R σ J) Subtype.val (ν.map (hermOne R h))
      {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} Φ g) :
    IsContDensityOn μ (fun X => qR R σ J (X 0)) id ν B Φ (fun s => g (hermOne R h s)) := by
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have key := density_comp (V := Fin 1 → Fin M → R ⊗[F] E) (Z := Matrix (Fin 1) (Fin 1) (R ⊗[F] E))
    (hermOne R h) (μ := μ) (ν := ν) (f := gramR R σ J) (ι := Subtype.val) Subtype.val_injective
    (f' := fun X => qR R σ J (X 0)) (fun X => gram_hermOne R h hJ X)
    (B' := {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}) (B := B)
    (fun s hs => unit_hermOne R h (hB s hs)) (Φ := Φ) (g := g)
  exact key hd

end Sd

/- English proof (translation)
Conclude with `(hP F E σ h M J hJ).2 n hn T hT hd d b Φ Φinf Φf Φv h1 (rapid_of_compact b h1 h2) ⟨h2, h3⟩ h4 h5`.
-/
theorem gram_form (hP : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (n : ℕ) (hn : 2 * n < M)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hd : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (h1 : Continuous Φinf) (h2 : HasCompactSupport Φinf)
    (h3 : ∀ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φinf ∘ e.symm))
    (h4 : IsPureFin b Φf Φv) (h5 : IsProdInfFin Φ Φinf Φf) :
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thSum F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT) := by
  exact (hP F E σ h M J hJ).2 n hn T hT hd d b Φ Φinf Φf Φv h1 (rapid_of_compact b h1 h2) ⟨h2, h3⟩ h4 h5

end GlobalTheory.GaussMean.OneVec

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice OneVec

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h M J hJ`. Use `⟨(hP F E σ h M J hJ).1, ?_⟩` and prove the remaining obligations. Introduce `hM β hβ d b Φ Φi Φf Φv h1 h2 h3 h4 h5`. Establish `hd : Matrix.det (fun _ _ : Fin 1 => algebraMap F E β) ≠ 0` using `fun h0 => hβ ((map_eq_zero _).mp ((Matrix.det_fin_one _).symm.trans h0))`. Establish `G` using `gram_form hP h hJ 1 (by omega) (fun _ _ => algebraMap F E β) (fun _ _ => σ.commutes β) hd d b Φ Φi Φf Φv h1 h2 h3 h4 h5`.

Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Establish `: ∀ v, BorelSpace (Fv F v)` using `fun v => ⟨rfl⟩`. Take `⟨⟨μ0, hμ0⟩, Gμ⟩` from `G`. Take `⟨⟨𝓕0, h𝓕0⟩, G𝓕⟩` from `Gμ μ0 hμ0`. Take `⟨⟨ψ0, hψ0⟩, -⟩` from `G𝓕 𝓕0 h𝓕0`.

Use `⟨⟨ψ0, hψ0⟩, fun ψ hψ => ?_⟩` and prove the remaining obligations. Use `⟨⟨μ0, hμ0⟩, fun μ hμ => ?_⟩` and prove the remaining obligations. Take `⟨⟨𝓕1, h𝓕1⟩, Gμ'⟩` from `Gμ μ hμ`. Use `⟨⟨𝓕1, h𝓕1⟩, fun 𝓕 h𝓕 => ?_⟩` and prove the remaining obligations. Take `⟨-, Gψ⟩` from `Gμ' 𝓕 h𝓕`.

Take `⟨⟨μi0, hμi0⟩, G2⟩` from `Gψ ψ hψ`. Take `⟨⟨νi0, hνi0⟩, G3⟩` from `G2 μi0 hμi0`. Take `⟨⟨μv0, hμv0⟩, G4⟩` from `G3 νi0 hνi0`. Take `⟨⟨νv0, hνv0⟩, -⟩` from `G4 μv0 hμv0`. Use `⟨⟨μi0, hμi0⟩, ⟨_, sd_of_herm h (ψ := psiInf F ψ) hνi0⟩, ⟨μv0, hμv0⟩, ⟨fun v => (νv0 v).map (hermOne (Fv F v) h).symm, fun v => sd_of_herm h (ψ := psiV F ψ v) (hνv0 v)⟩, ?_⟩` and prove the remaining obligations.

Introduce `μi νi μv νv hμi hνi hμv hνv`. Take `⟨-, G3'⟩` from `G2 μi hμi`. Take `⟨-, G4'⟩` from `G3' (νi.map (hermOne (Ainf F) h)) (sd_to_herm h (ψ := psiInf F ψ) hνi)`. Take `⟨-, G5'⟩` from `G4' μv hμv`. Take `⟨ginf, gv, hdi, hdv, hmul, hmean⟩` from `G5' (fun v => (νv v).map (hermOne (Fv F v) h)) (fun v => sd_to_herm h (ψ := psiV F ψ v) (hνv v))`.

Use `⟨fun s => ginf (hermOne (Ainf F) h s), fun v s => gv v (hermOne (Fv F v) h s), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `dens_of_herm h hJ (fun s hs => hs) hdi`. Introduce `v`. Conclude with `dens_of_herm h hJ (fun s hs => isUnit_iff_ne_zero.mpr hs) (hdv v)`. Simplify `hmul` using `only [hermOf_eq _ h]`.

Establish `hS : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β} = {x | hE σ J (x 0) (x 0) = algebraMap F E β}`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hX`.

Conclude with `congrFun (congrFun hX 0) 0`. Introduce `hX`. Use function extensionality and compare the values at `a c`. Rewrite using `[Subsingleton.elim a 0, Subsingleton.elim c 0]`. Conclude with `hX`.

Rewrite using `[← hS]`. Simplify `hmean` using `only [hermOf_eq _ h]`.
-/
theorem oneVectorCc_of_siegelWeil (hP : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) : OneVectorCc := by
  intro F E _ _ _ _ _ σ h M J hJ
  refine ⟨(hP F E σ h M J hJ).1, ?_⟩
  intro hM β hβ d b Φ Φi Φf Φv h1 h2 h3 h4 h5
  have hd : Matrix.det (fun _ _ : Fin 1 => algebraMap F E β) ≠ 0 :=
    fun h0 => hβ ((map_eq_zero _).mp ((Matrix.det_fin_one _).symm.trans h0))
  have G := gram_form hP h hJ 1 (by omega) (fun _ _ => algebraMap F E β) (fun _ _ => σ.commutes β) hd
    d b Φ Φi Φf Φv h1 h2 h3 h4 h5
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨⟨μ0, hμ0⟩, Gμ⟩ := G
  obtain ⟨⟨𝓕0, h𝓕0⟩, G𝓕⟩ := Gμ μ0 hμ0
  obtain ⟨⟨ψ0, hψ0⟩, -⟩ := G𝓕 𝓕0 h𝓕0
  refine ⟨⟨ψ0, hψ0⟩, fun ψ hψ => ?_⟩
  refine ⟨⟨μ0, hμ0⟩, fun μ hμ => ?_⟩
  obtain ⟨⟨𝓕1, h𝓕1⟩, Gμ'⟩ := Gμ μ hμ
  refine ⟨⟨𝓕1, h𝓕1⟩, fun 𝓕 h𝓕 => ?_⟩
  obtain ⟨-, Gψ⟩ := Gμ' 𝓕 h𝓕
  obtain ⟨⟨μi0, hμi0⟩, G2⟩ := Gψ ψ hψ
  obtain ⟨⟨νi0, hνi0⟩, G3⟩ := G2 μi0 hμi0
  obtain ⟨⟨μv0, hμv0⟩, G4⟩ := G3 νi0 hνi0
  obtain ⟨⟨νv0, hνv0⟩, -⟩ := G4 μv0 hμv0
  refine ⟨⟨μi0, hμi0⟩, ⟨_, sd_of_herm h (ψ := psiInf F ψ) hνi0⟩, ⟨μv0, hμv0⟩,
    ⟨fun v => (νv0 v).map (hermOne (Fv F v) h).symm, fun v => sd_of_herm h (ψ := psiV F ψ v) (hνv0 v)⟩, ?_⟩
  intro μi νi μv νv hμi hνi hμv hνv
  obtain ⟨-, G3'⟩ := G2 μi hμi
  obtain ⟨-, G4'⟩ := G3' (νi.map (hermOne (Ainf F) h)) (sd_to_herm h (ψ := psiInf F ψ) hνi)
  obtain ⟨-, G5'⟩ := G4' μv hμv
  obtain ⟨ginf, gv, hdi, hdv, hmul, hmean⟩ :=
    G5' (fun v => (νv v).map (hermOne (Fv F v) h)) (fun v => sd_to_herm h (ψ := psiV F ψ v) (hνv v))
  refine ⟨fun s => ginf (hermOne (Ainf F) h s), fun v s => gv v (hermOne (Fv F v) h s), ?_, ?_, ?_, ?_⟩
  · exact dens_of_herm h hJ (fun s hs => hs) hdi
  · intro v
    exact dens_of_herm h hJ (fun s hs => isUnit_iff_ne_zero.mpr hs) (hdv v)
  · simpa only [hermOf_eq _ h] using hmul
  · have hS : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β} =
        {x | hE σ J (x 0) (x 0) = algebraMap F E β} := by
      ext X
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hX
        exact congrFun (congrFun hX 0) 0
      · intro hX
        funext a c
        rw [Subsingleton.elim a 0, Subsingleton.elim c 0]
        exact hX
    rw [← hS]
    simpa only [hermOf_eq _ h] using hmean

end GlobalTheory.GaussMean
