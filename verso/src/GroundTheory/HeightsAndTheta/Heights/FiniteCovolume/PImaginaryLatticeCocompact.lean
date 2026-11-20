import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StImaginaryLatticeCocompact

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

/- English proof (translation)
Establish `h` using `embedding_conj (F := F) σ (algebraMap F E c)`. Rewrite `h` using `[conj_algebraMap]`. Conclude with `Complex.conj_eq_iff_im.mp h.symm`.
-/
theorem im_embedding_algebraMap (σ : E →+* ℂ) (c : F) : (σ (algebraMap F E c)).im = 0 := by
  have h := embedding_conj (F := F) σ (algebraMap F E c)
  rw [conj_algebraMap] at h
  exact Complex.conj_eq_iff_im.mp h.symm

omit [IsTotallyReal F] [IsTotallyComplex E] in
variable (F E) in

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_not_mem_range (F := F) (E := E)`. Take `⟨y, hy0, hyi⟩` from `(IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ ζ)).exists_integral_multiple`. Establish `hθF : y • ζ ∉ Set.range (algebraMap F E)`. Introduce and unpack `⟨c, hc⟩`. Apply `hζ` to reduce the goal to its premises.

Use `⟨(y : F)⁻¹ * c, ?_⟩` and prove the remaining obligations. Establish `hy : (y : E) ≠ 0` using `by exact_mod_cast hy0`. Rewrite using `[map_mul, hc, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]`. Establish `hcθ : IsIntegral ℤ (conj F E (y • ζ))` using `map_isIntegral_int ((conj F E : E ≃ₐ[F] E) : E →+* E) hyi`. Use `⟨⟨y • ζ - conj F E (y • ζ), hyi.sub hcθ⟩, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y • ζ - conj F E (y • ζ) ≠ 0`. Introduce `h`. Apply `hθF` to reduce the goal to its premises. Rewrite using `[← conj_eq_self_iff]`. Conclude with `(sub_eq_zero.mp h).symm`.

Express the relevant statement in the definitionally equal form `conj F E (y • ζ - conj F E (y • ζ)) = -(y • ζ - conj F E (y • ζ))`. Rewrite using `[map_sub, conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_imaginary_integer : ∃ t : 𝓞 E, (t : E) ≠ 0 ∧ conj F E (t : E) = -(t : E) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  obtain ⟨y, hy0, hyi⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ ζ)).exists_integral_multiple
  have hθF : y • ζ ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    apply hζ
    refine ⟨(y : F)⁻¹ * c, ?_⟩
    have hy : (y : E) ≠ 0 := by exact_mod_cast hy0
    rw [map_mul, hc, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  have hcθ : IsIntegral ℤ (conj F E (y • ζ)) :=
    map_isIntegral_int ((conj F E : E ≃ₐ[F] E) : E →+* E) hyi
  refine ⟨⟨y • ζ - conj F E (y • ζ), hyi.sub hcθ⟩, ?_, ?_⟩
  · change y • ζ - conj F E (y • ζ) ≠ 0
    intro h
    apply hθF
    rw [← conj_eq_self_iff]
    exact (sub_eq_zero.mp h).symm
  · change conj F E (y • ζ - conj F E (y • ζ)) = -(y • ζ - conj F E (y • ζ))
    rw [map_sub, conj_conj]
    ring

omit [IsTotallyReal F] in
variable (F E) in

/- English proof (translation)
Establish `h1` using `IsTotallyComplex.finrank (K := E)`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)`. Establish `h3` using `IsTotallyComplex.nrRealPlaces_eq_zero (K := E)`. Establish `h4` using `Module.finrank_mul_finrank ℚ F E`. Rewrite `h4` using `[Algebra.IsQuadraticExtension.finrank_eq_two F E]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_infinitePlace_eq : Fintype.card (InfinitePlace E) = finrank ℚ F := by
  have h1 := IsTotallyComplex.finrank (K := E)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
  have h4 := Module.finrank_mul_finrank ℚ F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h4
  omega

/- English proof (translation)
Introduce `m hm`. Take `⟨t, ht0, htc⟩` from `exists_imaginary_integer F E`. Set `L : Free.ChooseBasisIndex ℤ (𝓞 F) → InfinitePlace E → ℝ` to `fun i w => (w.embedding ((m : E) * algebraMap F E (integralBasis F i) * (t : E))).im`. Set `T : (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ)` to `{ toFun := fun c w => ∑ i, c i * L i w map_add' := by`. Introduce `c d`.

Use extensionality with `w`. Simplify using `[add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`. Introduce `r c`. Use extensionality with `w`.

Simplify using `[Finset.mul_sum, mul_assoc] }`. Establish `hr : ∀ w : InfinitePlace E, (w.embedding (t : E)).im ≠ 0`. Introduce `w h`. Establish `hre : (w.embedding (t : E)).re = 0`. Establish `h1` using `embedding_conj (F := F) w.embedding (t : E)`.

Rewrite `h1` using `[htc, map_neg]`. Establish `h2` using `congrArg Complex.re h1`. Simplify using `only [Complex.neg_re, Complex.conj_re] at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `ht0 ((map_eq_zero _).mp (Complex.ext hre h))`.

Establish `hL : ∀ i w, L i w = m * (w.embedding (algebraMap F E (integralBasis F i))).re * (w.embedding (t : E)).im`. Introduce `i w`. Simplify using `only [L, map_mul, map_natCast, Complex.mul_im, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, im_embedding_algebraMap]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective T`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Establish `hw : ∀ w : InfinitePlace E, ∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re = 0`. Introduce `w`. Establish `h1 : ∑ i, c i * L i w = 0` using `congrFun hc w`.

Establish `h2 : (∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re) * ((m : ℝ) * (w.embedding (t : E)).im) = 0`. Rewrite using `[Finset.sum_mul, ← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hL]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(mul_eq_zero.mp h2).resolve_right (mul_ne_zero (by exact_mod_cast hm.ne') (hr w))`. Establish `hτ : ∀ τ : F →+* ℂ, ∑ i, (c i : ℂ) * τ (integralBasis F i) = 0`. Introduce `τ`. Set `_ : Algebra F ℂ` to `τ.toAlgebra`. Set `σ : E →ₐ[F] ℂ` to `IsAlgClosed.lift`.

Establish `hστ : ∀ x : F, (σ : E →+* ℂ) (algebraMap F E x) = τ x` using `fun x => σ.commutes x`. Establish `hre : ∀ x : F, ((InfinitePlace.mk (σ : E →+* ℂ)).embedding (algebraMap F E x)).re = (τ x).re`. Introduce `x`. Break down `InfinitePlace.embedding_mk_eq (σ : E →+* ℂ) with h | h` into its components or cases. Rewrite using `[h, hστ]`.

Rewrite using `[h, ComplexEmbedding.conjugate_coe_eq, hστ, Complex.conj_re]`. Establish `him : ∀ x : F, (τ x).im = 0`. Introduce `x`. Rewrite using `[← hστ]`. Conclude with `im_embedding_algebraMap (F := F) (σ : E →+* ℂ) x`.

Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.re_sum, Complex.zero_re, ← hw (InfinitePlace.mk (σ : E →+* ℂ))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_ofReal_mul, hre]`. Rewrite using `[Complex.im_sum, Complex.zero_im]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.im_ofReal_mul, him, mul_zero]`. Establish `hli` using `(canonicalEmbedding.latticeBasis F).linearIndependent`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `i`.

Establish `h0` using `hli (fun i => (c i : ℂ)) (by`. Use function extensionality and compare the values at `τ`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]`. Conclude with `hτ τ) i`. Conclude with `h0` after adjusting the coercions.

Establish `hsurj : Function.Surjective T`. Use `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj` and prove the remaining obligations. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_infinitePlace_eq F E, finrank_eq_card_basis (integralBasis F)]`. Use `⟨∑ i, ∑ w, |L i w|, fun s => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hsurj s`.

Establish `hint : ∀ i, IsIntegral ℤ (algebraMap F E (integralBasis F i))`. Introduce `i`. Rewrite using `[integralBasis_apply]`. Conclude with `map_isIntegral_int (algebraMap F E) (RingOfIntegers.basis F i).2`. Establish `hk : ∀ k : ℤ, IsIntegral ℤ (k : E)` using `fun k => by`.

Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)`. Set `x : E` to `∑ i, (⌊c i⌋ : E) * algebraMap F E (integralBasis F i) * (t : E)`. Establish `hx : IsIntegral ℤ x` using `IsIntegral.sum _ fun i _ => ((hk _).mul (hint i)).mul t.2`. Use `⟨⟨x, hx⟩, ?_, fun w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : E) * x + conj F E ((m : E) * x) = 0`.

Establish `: conj F E x = -x`. Simplify using `only [x, map_sum, map_mul, map_intCast, conj_algebraMap, htc]`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_mul, map_natCast, this]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `|(w.embedding ((m : E) * x)).im - s w| ≤ ∑ i, ∑ w, |L i w|`. Establish `key : (w.embedding ((m : E) * x)).im = ∑ i, (⌊c i⌋ : ℝ) * L i w`. Establish `e : (m : E) * x = ∑ i, (⌊c i⌋ : E) * ((m : E) * algebraMap F E (integralBasis F i) * (t : E))`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_sum, Complex.im_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_intCast]`. Simplify using `[Complex.mul_im, L]`. Establish `hs : s w = ∑ i, c i * L i w` using `by rw [← hc]; rfl`. Rewrite using `[key, hs, ← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations.

Establish `h1 : |(⌊c i⌋ : ℝ) * L i w - c i * L i w| ≤ |L i w|`. Rewrite using `[← sub_mul, abs_mul]`. Establish `: |(⌊c i⌋ : ℝ) - c i| ≤ 1`. Rewrite using `[abs_sub_comm, abs_le]`. Apply the tactic sequence `constructor <;> linarith [Int.floor_le (c i), Int.lt_floor_add_one (c i)]`.

Conclude with `mul_le_of_le_one_left (abs_nonneg _) this`. Conclude with `h1.trans (Finset.single_le_sum (f := fun w' => |L i w'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w))`.
-/
theorem ImaginaryLatticeCocompact.proof : ImaginaryLatticeCocompact.Statement F E := by
  classical
  intro m hm
  obtain ⟨t, ht0, htc⟩ := exists_imaginary_integer F E
  let L : Free.ChooseBasisIndex ℤ (𝓞 F) → InfinitePlace E → ℝ := fun i w =>
    (w.embedding ((m : E) * algebraMap F E (integralBasis F i) * (t : E))).im
  let T : (Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
    { toFun := fun c w => ∑ i, c i * L i w
      map_add' := by
        intro c d; ext w; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c; ext w; simp [Finset.mul_sum, mul_assoc] }

  have hr : ∀ w : InfinitePlace E, (w.embedding (t : E)).im ≠ 0 := by
    intro w h
    have hre : (w.embedding (t : E)).re = 0 := by
      have h1 := embedding_conj (F := F) w.embedding (t : E)
      rw [htc, map_neg] at h1
      have h2 := congrArg Complex.re h1
      simp only [Complex.neg_re, Complex.conj_re] at h2
      linarith
    exact ht0 ((map_eq_zero _).mp (Complex.ext hre h))
  have hL : ∀ i w, L i w =
      m * (w.embedding (algebraMap F E (integralBasis F i))).re * (w.embedding (t : E)).im := by
    intro i w
    simp only [L, map_mul, map_natCast, Complex.mul_im, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, im_embedding_algebraMap]
    ring
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ w : InfinitePlace E,
        ∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re = 0 := by
      intro w
      have h1 : ∑ i, c i * L i w = 0 := congrFun hc w
      have h2 : (∑ i, c i * (w.embedding (algebraMap F E (integralBasis F i))).re) *
          ((m : ℝ) * (w.embedding (t : E)).im) = 0 := by
        rw [Finset.sum_mul, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hL]; ring
      exact (mul_eq_zero.mp h2).resolve_right
        (mul_ne_zero (by exact_mod_cast hm.ne') (hr w))
    have hτ : ∀ τ : F →+* ℂ, ∑ i, (c i : ℂ) * τ (integralBasis F i) = 0 := by
      intro τ
      let _ : Algebra F ℂ := τ.toAlgebra
      let σ : E →ₐ[F] ℂ := IsAlgClosed.lift
      have hστ : ∀ x : F, (σ : E →+* ℂ) (algebraMap F E x) = τ x := fun x => σ.commutes x
      have hre : ∀ x : F,
          ((InfinitePlace.mk (σ : E →+* ℂ)).embedding (algebraMap F E x)).re = (τ x).re := by
        intro x
        rcases InfinitePlace.embedding_mk_eq (σ : E →+* ℂ) with h | h
        · rw [h, hστ]
        · rw [h, ComplexEmbedding.conjugate_coe_eq, hστ, Complex.conj_re]
      have him : ∀ x : F, (τ x).im = 0 := by
        intro x
        rw [← hστ]
        exact im_embedding_algebraMap (F := F) (σ : E →+* ℂ) x
      apply Complex.ext
      · rw [Complex.re_sum, Complex.zero_re, ← hw (InfinitePlace.mk (σ : E →+* ℂ))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_ofReal_mul, hre]
      · rw [Complex.im_sum, Complex.zero_im]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Complex.im_ofReal_mul, him, mul_zero]
    have hli := (canonicalEmbedding.latticeBasis F).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    have h0 := hli (fun i => (c i : ℂ)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
      exact hτ τ) i
    exact_mod_cast h0
  have hsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      card_infinitePlace_eq F E, finrank_eq_card_basis (integralBasis F)]
  refine ⟨∑ i, ∑ w, |L i w|, fun s => ?_⟩
  obtain ⟨c, hc⟩ := hsurj s
  have hint : ∀ i, IsIntegral ℤ (algebraMap F E (integralBasis F i)) := by
    intro i
    rw [integralBasis_apply]
    exact map_isIntegral_int (algebraMap F E) (RingOfIntegers.basis F i).2
  have hk : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  let x : E := ∑ i, (⌊c i⌋ : E) * algebraMap F E (integralBasis F i) * (t : E)
  have hx : IsIntegral ℤ x :=
    IsIntegral.sum _ fun i _ => ((hk _).mul (hint i)).mul t.2
  refine ⟨⟨x, hx⟩, ?_, fun w => ?_⟩
  · change (m : E) * x + conj F E ((m : E) * x) = 0
    have : conj F E x = -x := by
      simp only [x, map_sum, map_mul, map_intCast, conj_algebraMap, htc]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [map_mul, map_natCast, this]
    ring
  · change |(w.embedding ((m : E) * x)).im - s w| ≤ ∑ i, ∑ w, |L i w|
    have key : (w.embedding ((m : E) * x)).im = ∑ i, (⌊c i⌋ : ℝ) * L i w := by
      have e : (m : E) * x = ∑ i, (⌊c i⌋ : E) * ((m : E) * algebraMap F E (integralBasis F i) * (t : E)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, map_sum, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_intCast]
      simp [Complex.mul_im, L]
    have hs : s w = ∑ i, c i * L i w := by rw [← hc]; rfl
    rw [key, hs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : |(⌊c i⌋ : ℝ) * L i w - c i * L i w| ≤ |L i w| := by
      rw [← sub_mul, abs_mul]
      have : |(⌊c i⌋ : ℝ) - c i| ≤ 1 := by
        rw [abs_sub_comm, abs_le]
        constructor <;> linarith [Int.floor_le (c i), Int.lt_floor_add_one (c i)]
      exact mul_le_of_le_one_left (abs_nonneg _) this
    exact h1.trans (Finset.single_le_sum (f := fun w' => |L i w'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
