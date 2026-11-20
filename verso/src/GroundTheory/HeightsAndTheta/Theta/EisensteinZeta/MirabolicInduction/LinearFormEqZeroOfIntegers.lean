import Mathlib
import GroundTheory.HeightsAndTheta.Theta.UnitaryReduction.UnipotentRadicalPlaces
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

namespace DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate

section NumberFieldFacts

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

open Classical

/- English proof (translation)
Use extensionality with `φ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : InfinitePlace.mk w.embedding = InfinitePlace.mk φ` using `by rw [mk_embedding, h]`.

Break down `InfinitePlace.mk_eq_iff.mp h' with h1 | h1` into its components or cases. Conclude with `Or.inl h1.symm`. Conclude with `Or.inr h1.symm`. Introduce and unpack `(h | h)`. Rewrite using `[h, mk_embedding]`.

Rewrite using `[h, mk_conjugate_eq, mk_embedding]`.
-/
private theorem filter_mk_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk φ := by rw [mk_embedding, h]
    rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  · rintro (h | h)
    · rw [h, mk_embedding]
    · rw [h, mk_conjugate_eq, mk_embedding]

/- English proof (translation)
Introduce `h`. Establish `hr : InfinitePlace.IsReal w` using `InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm)`. Conclude with `(not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hr`.
-/
private theorem embedding_ne_conjugate (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hr : InfinitePlace.IsReal w := InfinitePlace.isReal_iff.mpr
    (ComplexEmbedding.isReal_iff.mpr h.symm)
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hr

/- English proof (translation)
Establish `h1 : (algebraMap ℚ ℂ (Algebra.trace ℚ E t)) = ∑ σ : E →ₐ[ℚ] ℂ, σ t` using `trace_eq_sum_embeddings (E := ℂ)`. Establish `h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ φ : E →+* ℂ, φ t` using `(Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ t)).symm`. Establish `h3 : ∑ φ : E →+* ℂ, φ t = ∑ w : InfinitePlace E, ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ t` using `(Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ t)).symm`. Establish `h4 : ∀ w : InfinitePlace E, ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ t = ((2 * (w.embedding t).re : ℝ) : ℂ)`. Introduce `w`.

Rewrite using `[filter_mk_eq, Finset.sum_pair (embedding_ne_conjugate w), ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]`. Establish `h5 : ((Algebra.trace ℚ E t : ℝ) : ℂ) = ((∑ w : InfinitePlace E, 2 * (w.embedding t).re : ℝ) : ℂ)`. Rewrite using `[show ((Algebra.trace ℚ E t : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E t) by simp, h1, h2, h3]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [h4 w]; push_cast; ring`.

Establish `h6` using `Complex.ofReal_injective h5`. Rewrite using `[h6, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_re_embedding (t : E) :
    ∑ τ : InfinitePlace E, (τ.embedding t).re = (Algebra.trace ℚ E t : ℝ) / 2 := by
  have h1 : (algebraMap ℚ ℂ (Algebra.trace ℚ E t)) = ∑ σ : E →ₐ[ℚ] ℂ, σ t :=
    trace_eq_sum_embeddings (E := ℂ)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ φ : E →+* ℂ, φ t :=
    (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ t)).symm
  have h3 : ∑ φ : E →+* ℂ, φ t =
      ∑ w : InfinitePlace E, ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
        φ t :=
    (Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ t)).symm
  have h4 : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ t =
        ((2 * (w.embedding t).re : ℝ) : ℂ) := by
    intro w
    rw [filter_mk_eq, Finset.sum_pair (embedding_ne_conjugate w), ComplexEmbedding.conjugate_coe_eq,
      Complex.add_conj]
  have h5 : ((Algebra.trace ℚ E t : ℝ) : ℂ) =
      ((∑ w : InfinitePlace E, 2 * (w.embedding t).re : ℝ) : ℂ) := by
    rw [show ((Algebra.trace ℚ E t : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E t) by simp,
      h1, h2, h3]
    push_cast
    exact Finset.sum_congr rfl fun w _ => by rw [h4 w]; push_cast; ring
  have h6 := Complex.ofReal_injective h5
  rw [h6, ← Finset.mul_sum]; ring

/- English proof (translation)
Set `Ψ : mixedEmbedding.mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ)` to `{ toFun := fun p τ => if hτ : InfinitePlace.IsComplex τ then p.2 ⟨τ, hτ⟩ else 0 map_add' := fun p q => by`. Apply the tactic sequence `funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ]`. Use the proof step `map_smul' := fun r p => by`. Apply the tactic sequence `funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ] }`. Establish `hΨ : ∀ x : E, Ψ (mixedEmbedding E x) = fun τ => τ.embedding x`.

Introduce `x`. Use function extensionality and compare the values at `τ`. Establish `hτ : InfinitePlace.IsComplex τ` using `IsTotallyComplex.isComplex τ`. Simplify using `[Ψ, hτ, mixedEmbedding.mixedEmbedding_apply_isComplex]`. Establish `hzero : Λ ∘ₗ Ψ = 0`.

Use `(mixedEmbedding.latticeBasis E).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply, hΨ, LinearMap.zero_apply]`. Conclude with `h _`. Establish `hw : Ψ ((0, fun v => w v.1) : mixedEmbedding.mixedSpace E) = w`. Use function extensionality and compare the values at `τ`.

Establish `hτ : InfinitePlace.IsComplex τ` using `IsTotallyComplex.isComplex τ`. Simplify using `[Ψ, hτ]`. Rewrite using `[← hw, ← LinearMap.comp_apply, hzero, LinearMap.zero_apply]`.
-/
theorem linearForm_eq_zero_of_integers (Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ)
    (h : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0) (w : InfinitePlace E → ℂ) :
    Λ w = 0 := by
  classical
  let Ψ : mixedEmbedding.mixedSpace E →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    { toFun := fun p τ => if hτ : InfinitePlace.IsComplex τ then p.2 ⟨τ, hτ⟩ else 0
      map_add' := fun p q => by
        funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ]
      map_smul' := fun r p => by
        funext τ; by_cases hτ : InfinitePlace.IsComplex τ <;> simp [hτ] }
  have hΨ : ∀ x : E, Ψ (mixedEmbedding E x) = fun τ => τ.embedding x := by
    intro x; funext τ
    have hτ : InfinitePlace.IsComplex τ := IsTotallyComplex.isComplex τ
    simp [Ψ, hτ, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hzero : Λ ∘ₗ Ψ = 0 := by
    refine (mixedEmbedding.latticeBasis E).ext fun i => ?_
    rw [LinearMap.comp_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply, hΨ,
      LinearMap.zero_apply]
    exact h _
  have hw : Ψ ((0, fun v => w v.1) : mixedEmbedding.mixedSpace E) = w := by
    funext τ
    have hτ : InfinitePlace.IsComplex τ := IsTotallyComplex.isComplex τ
    simp [Ψ, hτ]
  rw [← hw, ← LinearMap.comp_apply, hzero, LinearMap.zero_apply]

end NumberFieldFacts

section DualLattice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`. Rewrite using `[FractionalIdeal.mem_singleton_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ c`. Rewrite `hy` using `[invDiff, FractionalIdeal.mem_dual h1]`.

Take `⟨n, hn⟩` from `hy (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[Algebra.traceForm_apply]`. Establish `: (c : E) * (2 * y) = (2 : ℚ) • (y * c)`. Rewrite using `[Algebra.smul_def, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, LinearMap.map_smul, ← hn]`. Simplify using the standard rewrite rules. Introduce `h`. Use `⟨(2 : E)⁻¹ * t, ?_, by field_simp⟩` and prove the remaining obligations.

Rewrite using `[invDiff, FractionalIdeal.mem_dual h1]`. Introduce `a ha`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨n, hn⟩` from `h c`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.traceForm_apply]`. Establish `: (2 : E)⁻¹ * t * algebraMap (𝓞 E) E c = (2⁻¹ : ℚ) • ((c : E) * t)`. Rewrite using `[Algebra.smul_def]`. Simplify using `only [map_inv₀, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, LinearMap.map_smul, hn]`. Simplify using the standard rewrite rules.
-/
theorem mem_two_invDiff_iff (t : E) :
    t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E ↔
      ∀ c : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((c : E) * t) = 2 * n := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩ c
    rw [invDiff, FractionalIdeal.mem_dual h1] at hy
    obtain ⟨n, hn⟩ := hy (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    have : (c : E) * (2 * y) = (2 : ℚ) • (y * c) := by
      rw [Algebra.smul_def, map_ofNat]; ring
    rw [this, LinearMap.map_smul, ← hn]
    simp
  · intro h
    refine ⟨(2 : E)⁻¹ * t, ?_, by field_simp⟩
    rw [invDiff, FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := h c
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    have : (2 : E)⁻¹ * t * algebraMap (𝓞 E) E c = (2⁻¹ : ℚ) • ((c : E) * t) := by
      rw [Algebra.smul_def]; simp only [map_inv₀, map_ofNat]; ring
    rw [this, LinearMap.map_smul, hn]
    simp

/- English proof (translation)
Set `b` to `integralBasis E`. Use `choose n hn using fun i => hz (RingOfIntegers.basis E i)`. Establish `hB` using `traceForm_nondegenerate ℚ E`. Set `db` to `(Algebra.traceForm ℚ E).dualBasis hB b`. Set `t : E` to `∑ i, ((2 * n i : ℤ) : ℚ) • db i`.

Set `L1 : E →ₗ[ℚ] ℝ` to `{ toFun := fun e => ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2 map_add' := fun x y => by rw [add_mul, map_add, Rat.cast_add, add_div] map_smul' := fun q x => by`. Rewrite using `[smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, Rat.cast_mul, RingHom.id_apply, Rat.smul_def]`. Use `ring }`. Set `L2 : E →ₗ[ℚ] ℝ` to `{ toFun := fun e => ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re map_add' := fun x y => by`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun τ _ => by rw [map_add, add_mul, Complex.add_re]`. Use the proof step `map_smul' := fun q x => by`. Simplify using `only [RingHom.id_apply, Rat.smul_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_ratCast, mul_assoc, show ((q : ℂ)) = ((q : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul] }`.

Establish `hbt : ∀ j, Algebra.trace ℚ E (b j * t) = 2 * n j`. Introduce `j`. Simplify using `only [t, Finset.mul_sum, mul_smul_comm, map_sum, LinearMap.map_smul, smul_eq_mul]`. Establish `: ∀ i, Algebra.trace ℚ E (b j * db i) = if j = i then 1 else 0`. Introduce `i`.

Rewrite using `[mul_comm, ← Algebra.traceForm_apply]`. Conclude with `LinearMap.BilinForm.apply_dualBasis_left hB b i j`. Simplify using `only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hL : L1 = L2`. Use `b.ext fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Algebra.trace ℚ E (b j * t) : ℚ) : ℝ) / 2 = ∑ τ : InfinitePlace E, (τ.embedding (b j) * z τ).re`. Rewrite using `[hbt j, integralBasis_apply]`. Use `hn j` as an intermediate fact.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap] at this ⊢`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hL' : ∀ e : E, ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2 = ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re` using `fun e => LinearMap.congr_fun hL e`.

Set `d : InfinitePlace E → ℂ` to `fun τ => z τ - τ.embedding t`. Set `Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ` to `{ toFun := fun w => ∑ τ : InfinitePlace E, (w τ * d τ).re map_add' := fun x y => by`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_mul, Complex.add_re]`. Use the proof step `map_smul' := fun r x => by`.

Rewrite using `[RingHom.id_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => by`. Rewrite using `[Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul] }`. Establish `hΛ : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0`. Introduce `c`.

Express the relevant statement in the definitionally equal form `∑ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re = 0`. Establish `e1 : ∀ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re = (τ.embedding (c : E) * z τ).re - (τ.embedding ((c : E) * t)).re`. Introduce `τ`. Simplify using `only [d, mul_sub, Complex.sub_re, map_mul]`. Rewrite using `[Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_sub_distrib, ← hL', sum_re_embedding]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ τ, d τ = 0`. Establish `h0` using `linearForm_eq_zero_of_integers Λ hΛ (fun τ => conj (d τ))`. Express the relevant statement in the definitionally equal form `∑ τ : InfinitePlace E, (conj (d τ) * d τ).re = 0 at h0`. Establish `hnn : ∀ τ ∈ Finset.univ, 0 ≤ (conj (d τ) * d τ).re` using `fun τ _ => by`.

Rewrite using `[← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`. Conclude with `Complex.normSq_nonneg _`. Introduce `τ`. Use `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 τ (Finset.mem_univ τ)` as an intermediate fact. Rewrite `this` using `[← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`.

Conclude with `Complex.normSq_eq_zero.mp this`. Use `⟨t, fun τ => sub_eq_zero.mp (hd τ), (mem_two_invDiff_iff t).mpr fun c => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hz c`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `hL' (c : E)` as an intermediate fact.

Rewrite `this` using `[hm]`. Conclude with `(by linarith : ((Algebra.trace ℚ E ((c : E) * t) : ℚ) : ℝ) = 2 * m)` after adjusting the coercions.
-/
theorem exists_of_integral_pairing (z : InfinitePlace E → ℂ)
    (hz : ∀ c : 𝓞 E, ∃ n : ℤ, ∑ τ : InfinitePlace E, (τ.embedding (c : E) * z τ).re = n) :
    ∃ t : E, (∀ τ, z τ = τ.embedding t) ∧
      t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E := by
  classical
  let b := integralBasis E
  choose n hn using fun i => hz (RingOfIntegers.basis E i)
  have hB := traceForm_nondegenerate ℚ E
  let db := (Algebra.traceForm ℚ E).dualBasis hB b
  let t : E := ∑ i, ((2 * n i : ℤ) : ℚ) • db i
  let L1 : E →ₗ[ℚ] ℝ :=
    { toFun := fun e => ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2
      map_add' := fun x y => by rw [add_mul, map_add, Rat.cast_add, add_div]
      map_smul' := fun q x => by
        rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, Rat.cast_mul, RingHom.id_apply,
          Rat.smul_def]
        ring }
  let L2 : E →ₗ[ℚ] ℝ :=
    { toFun := fun e => ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by rw [map_add, add_mul, Complex.add_re]
      map_smul' := fun q x => by
        simp only [RingHom.id_apply, Rat.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [map_mul, map_ratCast, mul_assoc,
          show ((q : ℂ)) = ((q : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul] }
  have hbt : ∀ j, Algebra.trace ℚ E (b j * t) = 2 * n j := by
    intro j
    simp only [t, Finset.mul_sum, mul_smul_comm, map_sum, LinearMap.map_smul, smul_eq_mul]
    have : ∀ i, Algebra.trace ℚ E (b j * db i) = if j = i then 1 else 0 := by
      intro i
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left hB b i j
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast; ring
  have hL : L1 = L2 := by
    refine b.ext fun j => ?_
    change ((Algebra.trace ℚ E (b j * t) : ℚ) : ℝ) / 2 = ∑ τ : InfinitePlace E, (τ.embedding (b j) * z τ).re
    rw [hbt j, integralBasis_apply]
    have := hn j
    simp only [RingOfIntegers.coe_eq_algebraMap] at this ⊢
    rw [this]; push_cast; ring
  have hL' : ∀ e : E, ((Algebra.trace ℚ E (e * t) : ℚ) : ℝ) / 2 =
      ∑ τ : InfinitePlace E, (τ.embedding e * z τ).re := fun e => LinearMap.congr_fun hL e
  let d : InfinitePlace E → ℂ := fun τ => z τ - τ.embedding t
  let Λ : (InfinitePlace E → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun w => ∑ τ : InfinitePlace E, (w τ * d τ).re
      map_add' := fun x y => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by rw [Pi.add_apply, add_mul, Complex.add_re]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by
          rw [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul] }
  have hΛ : ∀ c : 𝓞 E, Λ (fun τ => τ.embedding (c : E)) = 0 := by
    intro c
    change ∑ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re = 0
    have e1 : ∀ τ : InfinitePlace E, (τ.embedding (c : E) * d τ).re =
        (τ.embedding (c : E) * z τ).re - (τ.embedding ((c : E) * t)).re := by
      intro τ; simp only [d, mul_sub, Complex.sub_re, map_mul]
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_sub_distrib, ← hL', sum_re_embedding]
    ring
  have hd : ∀ τ, d τ = 0 := by
    have h0 := linearForm_eq_zero_of_integers Λ hΛ (fun τ => conj (d τ))
    change ∑ τ : InfinitePlace E, (conj (d τ) * d τ).re = 0 at h0
    have hnn : ∀ τ ∈ Finset.univ, 0 ≤ (conj (d τ) * d τ).re := fun τ _ => by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]; exact Complex.normSq_nonneg _
    intro τ
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 τ (Finset.mem_univ τ)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] at this
    exact Complex.normSq_eq_zero.mp this
  refine ⟨t, fun τ => sub_eq_zero.mp (hd τ), (mem_two_invDiff_iff t).mpr fun c => ?_⟩
  obtain ⟨m, hm⟩ := hz c
  refine ⟨m, ?_⟩
  have := hL' (c : E)
  rw [hm] at this
  exact_mod_cast (by linarith : ((Algebra.trace ℚ E ((c : E) * t) : ℚ) : ℝ) = 2 * m)

end DualLattice

section DualBasis

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Take `⟨bs, hbA, _hspan, hli⟩` from `exists_linearIndependent E (A : Set V)`. Set `bb` to `Basis.span hli`. Set `σ₀` to `bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))`. Take `⟨σ, hσ⟩` from `LinearMap.exists_extend σ₀`. Establish `hrange : Set.range ((↑) : bs → V) = bs` using `Subtype.range_coe`.

Establish `hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E)`. Introduce `i`. Establish `hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V))` using `Submodule.subset_span ⟨i, rfl⟩`. Establish `h1 : σ (i : V) = σ₀ ⟨i, hi⟩`. Rewrite using `[← hσ]`.

Both sides reduce to the same expression. Establish `h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i` using `by ext; rw [Basis.span_apply]`. Rewrite using `[h1, h2, Basis.constr_basis]`. Establish `hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A, σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E)`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => intro hxA`. Conclude with `hσb ⟨x, hx⟩`. Consider the case `zero => intro h0`. Simplify using `[show (⟨0, h0⟩ : A) = 0 from rfl]`.

Consider the case `add x y hx hy ihx ihy`. Introduce `hxyA`. Establish `hxA : x ∈ A` using `Submodule.span_le.mpr hbA hx`. Establish `hyA : y ∈ A` using `Submodule.span_le.mpr hbA hy`. Rewrite using `[map_add, ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl, map_add]`.

Use `push_cast`. Both sides reduce to the same expression. Consider the case `smul c x hx ihx`. Introduce `hcxA`. Establish `hxA : x ∈ A` using `Submodule.span_le.mpr hbA hx`.

Establish `e1 : σ (c • x) = (c : E) * σ x`. Rewrite using `[← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap]`. Establish `e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩`. Rewrite using `[show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]`. Rewrite using `[e1, e2, ihx hxA]`.

Simplify using the standard rewrite rules. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : (x : V) ∈ Submodule.span E (bs : Set V)`. Rewrite using `[_hspan]`. Conclude with `Submodule.subset_span x.2`.

Choose the witnesses or unpack the hypotheses as in `⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧ (x : V) = ∑ i, c i • v i := by`. Take `⟨m, c, g, hg⟩` from `(Submodule.mem_span_set').mp hx`. Conclude with `⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c`. Use `choose o ho using fun i => hd i (Finset.mem_univ i)`.

Establish `hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i`. Rewrite using `[hxv, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul, RingOfIntegers.coe_eq_algebraMap]`. Establish `hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V)` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))`.

Establish `hyA : ∑ i, o i • v i ∈ A` using `Submodule.span_le.mpr hbA hyP`. Establish `key` using `hP _ hyP hyA`. Establish `hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(∑ i, o i • v i) = (d : 𝓞 E) • (x : V)`.

Rewrite using `[← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]`. Rewrite `key` using `[hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul]`. Establish `hd0 : ((d : 𝓞 E) : E) ≠ 0` using `fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)`. Move the coercions through the operations in `at key`. Conclude with `mul_left_cancel₀ hd0 key`.
-/
theorem exists_extend_of_submodule (A : Submodule (𝓞 E) V) (s : A →ₗ[𝓞 E] 𝓞 E) :
    ∃ σ : V →ₗ[E] E, ∀ x : A, σ (x : V) = ((s x : 𝓞 E) : E) := by
  classical
  obtain ⟨bs, hbA, _hspan, hli⟩ := exists_linearIndependent E (A : Set V)
  let bb := Basis.span hli
  let σ₀ := bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend σ₀
  have hrange : Set.range ((↑) : bs → V) = bs := Subtype.range_coe
  have hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E) := by
    intro i
    have hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : σ (i : V) = σ₀ ⟨i, hi⟩ := by
      rw [← hσ]; rfl
    have h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i := by
      ext; rw [Basis.span_apply]
    rw [h1, h2, Basis.constr_basis]

  have hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A,
      σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hxA; exact hσb ⟨x, hx⟩
    | zero => intro h0; simp [show (⟨0, h0⟩ : A) = 0 from rfl]
    | add x y hx hy ihx ihy =>
      intro hxyA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have hyA : y ∈ A := Submodule.span_le.mpr hbA hy
      rw [map_add, ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl,
        map_add]
      push_cast; rfl
    | smul c x hx ihx =>
      intro hcxA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have e1 : σ (c • x) = (c : E) * σ x := by
        rw [← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul,
          RingOfIntegers.coe_eq_algebraMap]
      have e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩ := by
        rw [show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]
      rw [e1, e2, ihx hxA]
      simp
  refine ⟨σ, fun x => ?_⟩
  have hx : (x : V) ∈ Submodule.span E (bs : Set V) := by
    rw [_hspan]; exact Submodule.subset_span x.2
  obtain ⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧
      (x : V) = ∑ i, c i • v i := by
    obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').mp hx
    exact ⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c
  choose o ho using fun i => hd i (Finset.mem_univ i)
  have hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul,
      RingOfIntegers.coe_eq_algebraMap]
  have hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))
  have hyA : ∑ i, o i • v i ∈ A := Submodule.span_le.mpr hbA hyP
  have key := hP _ hyP hyA
  have hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x := by
    apply Subtype.ext
    change (∑ i, o i • v i) = (d : 𝓞 E) • (x : V)
    rw [← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]
  rw [hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul] at key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)
  push_cast at key
  exact mul_left_cancel₀ hd0 key

end DualBasis

section DualBasis2

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) A` using `Module.Finite.iff_fg.mpr hA`. Establish `: Module.Flat (𝓞 E) A`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff x).mp hx`.

Establish `h1 : ((a : 𝓞 E) : E) • (x : V) = 0`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]`. Conclude with `congrArg Subtype.val ha`. Establish `ha0 : ((a : 𝓞 E) : E) ≠ 0` using `fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)`. Establish `: Module.FinitePresentation (𝓞 E) A` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) A` using `Module.Flat.projective_of_finitePresentation`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' (𝓞 E) A`. Take `⟨h, hh⟩` from `Module.projective_lifting_property f LinearMap.id hf`.

Use `choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)`. Establish `hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V)`. Introduce `x`. Establish `h1 : x = f (h x)` using `(LinearMap.congr_fun hh x).symm`. Establish `h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E)`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [h1, h2]`. Rewrite using `[map_sum, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i), RingOfIntegers.coe_eq_algebraMap]`. Both sides reduce to the same expression. Use `⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `i x hx`. Conclude with `⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hxA ⟨y, hy⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => conv_lhs => rw [hy, hz]`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]`. Consider the case `smul c y _ hy => conv_lhs => rw [hy]`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]`.
-/
theorem exists_dualBasis (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by
  classical
  have : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.mpr hA
  have : Module.Flat (𝓞 E) A := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h1 : ((a : 𝓞 E) : E) • (x : V) = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
      exact congrArg Subtype.val ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)
  have : Module.FinitePresentation (𝓞 E) A := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) A := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) A
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)
  have hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V) := by
    intro x
    have h1 : x = f (h x) := (LinearMap.congr_fun hh x).symm
    have h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i),
      RingOfIntegers.coe_eq_algebraMap]
    rfl
  refine ⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩
  · intro i x hx
    exact ⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hxA ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz =>
      conv_lhs => rw [hy, hz]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
    | smul c y _ hy =>
      conv_lhs => rw [hy]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end DualBasis2

section Fibres

variable {E : Type} [Field E] [NumberField E]

variable (S : MetSpace E) (τ : InfinitePlace E)

/- English proof (translation)
The claim follows from `TensorProduct.tmul_add _ _ _`.
-/
theorem pt_add' (x y : S.V) : S.pt τ (x + y) = S.pt τ x + S.pt τ y := TensorProduct.tmul_add _ _ _

/- English proof (translation)
The claim follows from `TensorProduct.tmul_zero _ _`.
-/
theorem pt_zero' : S.pt τ 0 = 0 := TensorProduct.tmul_zero _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : CAt τ.embedding) ⊗ₜ[E] (e • x) = τ.embedding e • ((1 : CAt τ.embedding) ⊗ₜ[E] x)`. Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul', CAt.smul_def, CAt.complex_smul_def]`.
-/
theorem pt_smul' (e : E) (x : S.V) : S.pt τ (e • x) = τ.embedding e • S.pt τ x := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (e • x) = τ.embedding e • ((1 : CAt τ.embedding) ⊗ₜ[E] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', CAt.smul_def, CAt.complex_smul_def]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : CAt τ.embedding) ⊗ₜ[E] (∑ i ∈ s, c i • v i) = _`. Rewrite using `[TensorProduct.tmul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => pt_smul' S τ (c i) (v i)`.
-/
theorem pt_sum_smul' {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → S.V) :
    S.pt τ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, τ.embedding (c i) • S.pt τ (v i) := by
  change (1 : CAt τ.embedding) ⊗ₜ[E] (∑ i ∈ s, c i • v i) = _
  rw [TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => pt_smul' S τ (c i) (v i)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ⊗ₜ[E] v = (CAt.ofComplex τ.embedding).symm z • ((1 : CAt τ.embedding) ⊗ₜ[E] v)`. Rewrite using `[TensorProduct.smul_tmul', CAt.complex_smul_def, AlgEquiv.apply_symm_apply, mul_one]`.
-/
theorem tmul_eq_smul_pt (z : CAt τ.embedding) (v : S.V) :
    (z ⊗ₜ[E] v : S.FibSp τ) = (CAt.ofComplex τ.embedding).symm z • S.pt τ v := by
  change z ⊗ₜ[E] v = (CAt.ofComplex τ.embedding).symm z • ((1 : CAt τ.embedding) ⊗ₜ[E] v)
  rw [TensorProduct.smul_tmul', CAt.complex_smul_def, AlgEquiv.apply_symm_apply, mul_one]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨y, rfl⟩`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `tmul z w`. Rewrite using `[TensorProduct.AlgebraTensorModule.lTensor_tmul]`. Establish `hmem : S.pt τ (w : S.V) ∈ Submodule.span ℂ (S.pt τ '' (W : Set S.V))` using `Submodule.subset_span ⟨w, w.2, rfl⟩`. Establish `h2` using `(Submodule.span ℂ (S.pt τ '' (W : Set S.V))).smul_mem ((CAt.ofComplex τ.embedding).symm z) hmem`. Rewrite `h2` using `[← tmul_eq_smul_pt]`.

Conclude with `h2`. Consider the case `add y y' hy hy' => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hy'`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Conclude with `⟨(1 : CAt τ.embedding) ⊗ₜ[E] (⟨w, hw⟩ : W), by`. Rewrite using `[TensorProduct.AlgebraTensorModule.lTensor_tmul]`. Use the proof step `rfl⟩`.
-/
theorem fibSub_eq_span (W : Submodule E S.V) :
    S.fibSub W τ = Submodule.span ℂ (S.pt τ '' (W : Set S.V)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z w =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      have hmem : S.pt τ (w : S.V) ∈ Submodule.span ℂ (S.pt τ '' (W : Set S.V)) :=
        Submodule.subset_span ⟨w, w.2, rfl⟩
      have h2 := (Submodule.span ℂ (S.pt τ '' (W : Set S.V))).smul_mem
        ((CAt.ofComplex τ.embedding).symm z) hmem
      rw [← tmul_eq_smul_pt] at h2
      exact h2
    | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(1 : CAt τ.embedding) ⊗ₜ[E] (⟨w, hw⟩ : W), by
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]; rfl⟩

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [pt_zero']`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [pt_add']`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul e x _ hx => rw [pt_smul']`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem pt_mem_span_of_mem_espan (A : Submodule (𝓞 E) S.V) {w : S.V} (hw : w ∈ espan A) :
    S.pt τ w ∈ Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [pt_zero']; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [pt_add']; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [pt_smul']; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[fibSub_eq_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `pt_mem_span_of_mem_espan S τ A hw`.

Conclude with `Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))`.
-/
theorem fibSub_espan_eq_span (A : Submodule (𝓞 E) S.V) :
    S.fibSub (espan A) τ = Submodule.span ℂ (S.pt τ '' (A : Set S.V)) := by
  rw [fibSub_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨w, hw, rfl⟩; exact pt_mem_span_of_mem_espan S τ A hw
  · exact Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul z v`. Rewrite using `[tmul_eq_smul_pt]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)`.

Consider the case `add y y' hy hy' => exact Submodule.add_mem _ hy hy'`.
-/
theorem mem_span_pt (y : S.FibSp τ) : y ∈ Submodule.span ℂ (Set.range (S.pt τ)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul z v =>
    rw [tmul_eq_smul_pt]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add y y' hy hy' => exact Submodule.add_mem _ hy hy'

/- English proof (translation)
Use extensionality with `y`. Proceed by induction on `mem_span_pt S τ y using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨v, rfl⟩ := hx`. Conclude with `h v`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, map_smul, hx]`.
-/
theorem ext_pt {M : Type} [AddCommGroup M] [Module ℂ M] {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ v, X (S.pt τ v) = Y (S.pt τ v)) : X = Y := by
  ext y
  induction mem_span_pt S τ y using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact h v
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fibMap_pt' (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (v : S.V) :
    S.fibMap T φ τ (S.pt τ v) = T.pt τ (φ v) := rfl

/- English proof (translation)
Rewrite using `[fibSub_eq_span]`. Proceed by induction on `mem_span_pt S τ y using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Rewrite using `[fibMap_pt']`.

Conclude with `Submodule.subset_span ⟨φ v, hφ v, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem fibMap_mem_fibSub (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (W : Submodule E T.V)
    (hφ : ∀ v, φ v ∈ W) (y : S.FibSp τ) : S.fibMap T φ τ y ∈ T.fibSub W τ := by
  rw [fibSub_eq_span]
  induction mem_span_pt S τ y using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

def fibFun (σ : S.V →ₗ[E] E) : S.FibSp τ →ₗ[ℂ] ℂ :=
  (S.dualFunctional τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) : S.FibSp τ →L[ℂ] ℂ)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(CAt.ofComplex τ.embedding).symm (S.dualCoord τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) ((1 : CAt τ.embedding) ⊗ₜ[E] v)) = _`. Rewrite using `[dualCoord_tmul_tmul, one_mul, mul_one, CAt.algebraMap_apply, AlgEquiv.symm_apply_apply]`.
-/
theorem fibFun_pt (σ : S.V →ₗ[E] E) (v : S.V) :
    fibFun S τ σ (S.pt τ v) = τ.embedding (σ v) := by
  change (CAt.ofComplex τ.embedding).symm
    (S.dualCoord τ ((1 : CAt τ.embedding) ⊗ₜ[E] σ) ((1 : CAt τ.embedding) ⊗ₜ[E] v)) = _
  rw [dualCoord_tmul_tmul, one_mul, mul_one, CAt.algebraMap_apply, AlgEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite `hx` using `[fibSub_eq_span]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `hy`. Use `conv_lhs => rw [hid w hw, pt_sum_smul']`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [fibFun_pt]`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => conv_lhs => rw [hy, hz]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]`.

Consider the case `smul c y _ hy => conv_lhs => rw [hy]`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]`.
-/
theorem dualBasis_at (A : Submodule (𝓞 E) S.V) {n : ℕ} (a : Fin n → S.V) (σ : Fin n → (S.V →ₗ[E] E))
    (hid : ∀ x ∈ espan A, x = ∑ i, σ i x • a i) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) :
    x = ∑ i, fibFun S τ (σ i) x • S.pt τ (a i) := by
  rw [fibSub_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    conv_lhs => rw [hid w hw, pt_sum_smul']
    exact Finset.sum_congr rfl fun i _ => by rw [fibFun_pt]
  | zero => simp
  | add y z _ _ hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
  | smul c y _ hy =>
    conv_lhs => rw [hy]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]

end Fibres

section Adjoints

variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁), LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.adjoint_inner_right, inner_conj_symm]`.
-/
theorem trace_adjoint' (T : H₁ →ₗ[ℂ] H₁) :
    LinearMap.trace ℂ H₁ (LinearMap.adjoint T) = conj (LinearMap.trace ℂ H₁ T) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H₁), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.adjoint_inner_right, inner_conj_symm]

/- English proof (translation)
Establish `e1 : LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y) = LinearMap.trace ℂ H₁ (LinearMap.adjoint Y ∘ₗ X)`. Rewrite using `[LinearMap.trace_comp_comm']`. Establish `e2 : LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X) = LinearMap.trace ℂ H₁ (LinearMap.adjoint X ∘ₗ Y)`. Rewrite using `[LinearMap.trace_comp_comm']`. Establish `e3 : LinearMap.adjoint (LinearMap.adjoint Y ∘ₗ X) = LinearMap.adjoint X ∘ₗ Y`.

Rewrite using `[LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]`. Rewrite using `[e1, e2, ← e3, trace_adjoint', Complex.conj_re]`.
-/
theorem re_trace_comp_adjoint (X Y : H₁ →ₗ[ℂ] H₂) :
    (LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y)).re =
      (LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X)).re := by
  have e1 : LinearMap.trace ℂ H₂ (X ∘ₗ LinearMap.adjoint Y) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint Y ∘ₗ X) := by
    rw [LinearMap.trace_comp_comm']
  have e2 : LinearMap.trace ℂ H₂ (Y ∘ₗ LinearMap.adjoint X) =
      LinearMap.trace ℂ H₁ (LinearMap.adjoint X ∘ₗ Y) := by
    rw [LinearMap.trace_comp_comm']
  have e3 : LinearMap.adjoint (LinearMap.adjoint Y ∘ₗ X) = LinearMap.adjoint X ∘ₗ Y := by
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  rw [e1, e2, ← e3, trace_adjoint', Complex.conj_re]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y hy`. Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.adjoint_inner_right, inner_zero_right]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (h2 u) hy`.

Introduce `y`. Rewrite using `[← Submodule.orthogonal_orthogonal K₁, Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[LinearMap.adjoint_inner_right, h1 u hu, inner_zero_left]`.
-/
theorem adjoint_maps (X : H₁ →ₗ[ℂ] H₂) (K₁ : Submodule ℂ H₁) (K₂ : Submodule ℂ H₂)
    (h1 : ∀ y ∈ K₁ᗮ, X y = 0) (h2 : ∀ y, X y ∈ K₂) :
    (∀ y ∈ K₂ᗮ, LinearMap.adjoint X y = 0) ∧ ∀ y, LinearMap.adjoint X y ∈ K₁ := by
  constructor
  · intro y hy
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (h2 u) hy
  · intro y
    rw [← Submodule.orthogonal_orthogonal K₁, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.adjoint_inner_right, h1 u hu, inner_zero_left]

end Adjoints

section IdealMaps

variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, a, ha, rfl⟩` from `hy`. Rewrite using `[LinearMap.map_smul]`. Conclude with `Submodule.subset_span ⟨c, hc, U a, hU a ha, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_smulIdeal_mem (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V)
    (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V') (hU : ∀ a ∈ A, U a ∈ B) {x : V}
    (hx : x ∈ smulIdeal aa A) : U x ∈ smulIdeal aa B := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, rfl⟩ := hy
    rw [LinearMap.map_smul]
    exact Submodule.subset_span ⟨c, hc, U a, hU a ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, b, hb, rfl⟩` from `hy`. Take `⟨o, ho⟩` from `hρ b hb`. Rewrite using `[LinearMap.map_smul, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem _ o hc`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy => rw [LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem form_mem_of_smulIdeal (aa : FractionalIdeal (𝓞 E)⁰ E) (B : Submodule (𝓞 E) V)
    (ρ : V →ₗ[E] E) (hρ : ∀ b ∈ B, ρ b ∈ Set.range (algebraMap (𝓞 E) E)) {x : V}
    (hx : x ∈ smulIdeal aa B) : ρ x ∈ (aa : Submodule (𝓞 E) E) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, b, hb, rfl⟩ := hy
    obtain ⟨o, ho⟩ := hρ b hb
    rw [LinearMap.map_smul, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o hc
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, _, a, ha, rfl⟩` from `hy`. Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ha)`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add y z _ _ hy hz => exact Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy`. Rewrite using `[← algebraMap_smul E c y]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem mem_espan_of_smulIdeal (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ smulIdeal aa A) : x ∈ espan A := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, _, a, ha, rfl⟩ := hy
    exact Submodule.smul_mem _ c (Submodule.subset_span ha)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [← algebraMap_smul E c y]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hU y hy`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul e y _ hy => rw [LinearMap.map_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_espan_mem (A : Submodule (𝓞 E) V) (B : Submodule (𝓞 E) V') (U : V →ₗ[E] V')
    (hU : ∀ a ∈ A, U a ∈ espan B) {x : V} (hx : x ∈ espan A) : U x ∈ espan B := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hU y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hy

end IdealMaps

section FibMaps

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite `hy`, the goal using `[fibSub_eq_span]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Rewrite using `[fibMap_pt']`.

Conclude with `Submodule.subset_span ⟨φ v, hφ v hv, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x z _ _ hx hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hz`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem fibMap_fibSub (S T : MetSpace E) (τ : InfinitePlace E) (φ : S.V →ₗ[E] T.V)
    (W : Submodule E S.V) (W' : Submodule E T.V) (hφ : ∀ w ∈ W, φ w ∈ W') {y : S.FibSp τ}
    (hy : y ∈ S.fibSub W τ) : S.fibMap T φ τ y ∈ T.fibSub W' τ := by
  rw [fibSub_eq_span] at hy ⊢
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [fibMap_pt']; exact Submodule.subset_span ⟨φ v, hφ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite `hx` using `[fibSub_espan_eq_span]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨a, ha, rfl⟩ := hy`. Conclude with `h a ha`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add, map_add, hy, hz]`. Consider the case `smul c y _ hy => rw [map_smul, map_smul, hy]`.
-/
theorem eqOn_fibSub (S : MetSpace E) (τ : InfinitePlace E) {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : Submodule (𝓞 E) S.V) {X Y : S.FibSp τ →ₗ[ℂ] M}
    (h : ∀ a ∈ A, X (S.pt τ a) = Y (S.pt τ a)) {x : S.FibSp τ}
    (hx : x ∈ S.fibSub (espan A) τ) : X x = Y x := by
  rw [fibSub_espan_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, ha, rfl⟩ := hy; exact h a ha
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, hy]

/- English proof (translation)
Rewrite using `[fibSub_eq_span]`. Conclude with `Submodule.subset_span ⟨w, hw, rfl⟩`.
-/
theorem pt_mem_fibSub (S : MetSpace E) (τ : InfinitePlace E) (W : Submodule E S.V) {w : S.V}
    (hw : w ∈ W) : S.pt τ w ∈ S.fibSub W τ := by
  rw [fibSub_eq_span]; exact Submodule.subset_span ⟨w, hw, rfl⟩

end FibMaps

end DualHomPf

open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors

/- English proof (translation)
Introduce `S S' A B' hA hB'`. Take `⟨nb, b, ρ, hbB, hρO, hidB⟩` from `exists_dualBasis B' hB'`. Use extensionality with `T`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hTS, hTZ⟩`.

Take `⟨na, a, σ, haA, hσO, hidA⟩` from `exists_dualBasis A hA`. Establish `hwB : ∀ τ, ∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, LinearMap.adjoint (T τ) y = 0` using `fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).1`. Establish `hwA : ∀ τ y, LinearMap.adjoint (T τ) y ∈ S.fibSub (espan A) τ` using `fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).2`. Establish `hint : ∀ (i : Fin na) (j : Fin nb) (c : 𝓞 E), ∃ n : ℤ, ∑ τ : InfinitePlace E, (τ.embedding (c : E) * (fun τ : InfinitePlace E => fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))) τ).re = n`. Introduce `i j c`.

Set `U' : S.V →ₗ[E] S'.V` to `((c : E) • σ i).smulRight (b j)`. Establish `hU'v : ∀ v, U' v = ((c : E) * σ i v) • b j` using `fun v => by`. Simplify using `only [U', LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]`. Set `γ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ` to `fun τ => S.fibMap S' U' τ ∘ₗ ((S.fibSub (espan A) τ).starProjection : S.FibSp τ →ₗ[ℂ] S.FibSp τ)`. Establish `hγ : γ ∈ homImage A B'`.

Use `⟨fun τ => ⟨fun y hy => ?_, fun y => ?_⟩, U', fun x hx => ?_, fun τ x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]`. Conclude with `fibMap_mem_fibSub S τ S' U' (espan B') (fun v => by`. Rewrite using `[hU'v]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hbB j))) _`.

Take `⟨o, ho⟩` from `hσO i x hx`. Rewrite using `[hU'v, ← ho, RingOfIntegers.coe_eq_algebraMap, ← map_mul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (hbB j)`. Establish `hpt` using `pt_mem_fibSub S τ (espan A) (Submodule.subset_span hx : x ∈ espan A)`. Simplify using `only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.starProjection_eq_self_iff.mpr hpt]`.

Both sides reduce to the same expression. Take `⟨n, hn⟩` from `hTZ γ hγ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Establish `hU' : S.fibMap S' U' τ = ((τ.embedding (c : E)) • fibFun S τ (σ i)).smulRight (S'.pt τ (b j))`. Use `ext_pt S τ fun v => ?_` and prove the remaining obligations. Rewrite using `[fibMap_pt', hU'v, pt_smul', LinearMap.smulRight_apply, LinearMap.smul_apply, fibFun_pt, map_mul, smul_eq_mul]`. Establish `hcomp : γ τ ∘ₗ LinearMap.adjoint (T τ) = ((τ.embedding (c : E)) • (fibFun S τ (σ i) ∘ₗ LinearMap.adjoint (T τ))).smulRight (S'.pt τ (b j))`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Establish `hy` using `hwA τ y`. Simplify using `only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.starProjection_eq_self_iff.mpr hy, hU', LinearMap.smulRight_apply, LinearMap.smul_apply]`. Express the relevant statement in the definitionally equal form `(τ.embedding (c : E) * fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))).re = hsInner S (T τ) (γ τ)`. Unfold `hsInner`. Rewrite using `[re_trace_comp_adjoint (T τ) (γ τ), hcomp, LinearMap.trace_smulRight, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]`.

Use `choose t ht using fun i j => exists_of_integral_pairing _ (hint i j)`. Set `U : S'.V →ₗ[E] S.V` to `∑ j, (ρ j).smulRight (∑ i, t i j • a i)`. Establish `hUv : ∀ v, U v = ∑ j, ρ j v • ∑ i, t i j • a i` using `fun v => by`. Simplify using `only [U, LinearMap.sum_apply, LinearMap.smulRight_apply]`. Use `⟨U, fun y hy => ?_, fun τ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hUv]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `Submodule.subset_span ⟨ρ j y * t i j, ?_, a i, haA i, rfl⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `hρO j y hy`. Rewrite using `[← ho, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem (_ : Submodule (𝓞 E) E) o (ht i j).2`. Establish `hUfib : S'.fibMap S U τ = ∑ j, (fibFun S' τ (ρ j)).smulRight (S.pt τ (∑ i, t i j • a i))`.

Use `ext_pt S' τ fun v => ?_` and prove the remaining obligations. Rewrite using `[fibMap_pt', hUv, pt_sum_smul', LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [LinearMap.smulRight_apply, fibFun_pt]`. Establish `hwU : LinearMap.adjoint (T τ) = S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Establish `hperp` using `(S'.fibSub (espan B') τ).sub_starProjection_mem_orthogonal y`. Establish `hPB` using `(S'.fibSub (espan B') τ).starProjection_apply_mem y`. Establish `hsplit : y = (S'.fibSub (espan B') τ).starProjection y + (y - (S'.fibSub (espan B') τ).starProjection y)` using `by abel`. Rewrite using `[LinearMap.comp_apply, ContinuousLinearMap.coe_coe]`. Use `conv_lhs => rw [hsplit, map_add, hwB τ _ hperp, add_zero]`.

Generalize the expression as in `(S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢`. Establish `hx` using `dualBasis_at S' τ B' b ρ hidB hPB`. Use `conv_lhs => rw [hx]`. Rewrite using `[map_sum, hUfib, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, LinearMap.smulRight_apply]`. Use `congr 1`. Establish `hA'` using `dualBasis_at S τ A a σ hidA (hwA τ (S'.pt τ (b j)))`. Rewrite using `[hA', pt_sum_smul']`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [(ht i j).1 τ]`.

Rewrite using `[← hwU, LinearMap.adjoint_adjoint]`. Introduce and unpack `⟨U, hU, hT⟩`. Establish `hUE : ∀ y ∈ espan B', U y ∈ espan A` using `fun y hy => map_espan_mem B' A U (fun x hx => mem_espan_of_smulIdeal _ A (hU x hx)) hy`. Establish `hX : ∀ τ, (∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, (S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y = 0) ∧ ∀ y, (S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y ∈ S.fibSub (espan A) τ`. Introduce `τ`.

Use `⟨fun y hy => ?_, fun y => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]`. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]`. Conclude with `fibMap_fibSub S' S τ U (espan B') (espan A) hUE ((S'.fibSub (espan B') τ).starProjection_apply_mem y)`. Use `⟨fun τ => ?_, fun γ hγ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hT τ]`. Conclude with `adjoint_maps _ _ _ (hX τ).1 (hX τ).2`. Take `⟨_, U', hU'A, hγpt⟩` from `hγ`. Set `t : E` to `∑ j, ρ j (U' (U (b j)))`. Establish `ht : t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E`.

Use `Submodule.sum_mem (_ : Submodule (𝓞 E) E) fun j _ => ?_` and prove the remaining obligations. Conclude with `form_mem_of_smulIdeal _ B' (ρ j) (hρO j) (map_smulIdeal_mem _ A B' U' hU'A (hU (b j) (hbB j)))`. Take `⟨n, hn⟩` from `(mem_two_invDiff_iff t).mp ht 1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hU'E : ∀ y ∈ espan A, U' y ∈ espan B'` using `fun y hy => map_espan_mem A B' U' (fun x hx => Submodule.subset_span (hU'A x hx)) hy`.

Establish `hτ : ∀ τ : InfinitePlace E, hsInner S (T τ) (γ τ) = (τ.embedding t).re`. Introduce `τ`. Unfold `hsInner`. Rewrite using `[re_trace_comp_adjoint, hT τ, LinearMap.adjoint_adjoint]`. Establish `hγU : ∀ x ∈ S.fibSub (espan A) τ, γ τ x = S.fibMap S' U' τ x` using `fun x hx => eqOn_fibSub S τ A (fun a ha => by rw [hγpt τ a ha, fibMap_pt']) hx`.

Establish `hcomp : γ τ ∘ₗ (S'.fibMap S U τ ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) = ∑ j, ((fibFun S' τ (ρ j)) ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight (S'.pt τ (U' (U (b j))))`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.sum_apply, LinearMap.smulRight_apply]`. Establish `hPB` using `(S'.fibSub (espan B') τ).starProjection_apply_mem y`. Generalize the expression as in `(S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢`.

Establish `hx` using `dualBasis_at S' τ B' b ρ hidB hPB`. Use `conv_lhs => rw [hx]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, fibMap_pt', hγU _ (pt_mem_fibSub S τ (espan A) (hUE _ (Submodule.subset_span (hbB j)))), fibMap_pt']`.

Establish `hterm : ∀ j, LinearMap.trace ℂ (S'.FibSp τ) (((fibFun S' τ (ρ j)) ∘ₗ ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight (S'.pt τ (U' (U (b j))))) = τ.embedding (ρ j (U' (U (b j))))`. Introduce `j`. Rewrite using `[LinearMap.trace_smulRight, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.starProjection_eq_self_iff.mpr (pt_mem_fibSub S' τ (espan B') (hU'E _ (hUE _ (Submodule.subset_span (hbB j))))), fibFun_pt]`. Rewrite using `[hcomp, map_sum, Finset.sum_congr rfl fun j _ => hterm j, ← map_sum]`. Unfold `eucl`.

Rewrite using `[Finset.sum_congr rfl fun τ _ => hτ τ, sum_re_embedding]`. Establish `hn' : Algebra.trace ℚ E t = 2 * n` using `by simpa using hn`. Rewrite using `[hn']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualHom (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] :
    DualHom.Statement F E := by
  intro S S' A B' hA hB'
  obtain ⟨nb, b, ρ, hbB, hρO, hidB⟩ := exists_dualBasis B' hB'
  ext T
  constructor
  · rintro ⟨hTS, hTZ⟩
    obtain ⟨na, a, σ, haA, hσO, hidA⟩ := exists_dualBasis A hA
    have hwB : ∀ τ, ∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, LinearMap.adjoint (T τ) y = 0 :=
      fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).1
    have hwA : ∀ τ y, LinearMap.adjoint (T τ) y ∈ S.fibSub (espan A) τ :=
      fun τ => (adjoint_maps (T τ) _ _ (hTS τ).1 (hTS τ).2).2
    have hint : ∀ (i : Fin na) (j : Fin nb) (c : 𝓞 E), ∃ n : ℤ, ∑ τ : InfinitePlace E,
        (τ.embedding (c : E) *
          (fun τ : InfinitePlace E => fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))) τ).re
          = n := by
      intro i j c
      let U' : S.V →ₗ[E] S'.V := ((c : E) • σ i).smulRight (b j)
      have hU'v : ∀ v, U' v = ((c : E) * σ i v) • b j := fun v => by
        simp only [U', LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]
      let γ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S'.FibSp τ := fun τ =>
        S.fibMap S' U' τ ∘ₗ ((S.fibSub (espan A) τ).starProjection : S.FibSp τ →ₗ[ℂ] S.FibSp τ)
      have hγ : γ ∈ homImage A B' := by
        refine ⟨fun τ => ⟨fun y hy => ?_, fun y => ?_⟩, U', fun x hx => ?_, fun τ x hx => ?_⟩
        · simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]
        · exact fibMap_mem_fibSub S τ S' U' (espan B') (fun v => by
            rw [hU'v]; exact Submodule.smul_mem _ _ (Submodule.subset_span (hbB j))) _
        · obtain ⟨o, ho⟩ := hσO i x hx
          rw [hU'v, ← ho, RingOfIntegers.coe_eq_algebraMap, ← map_mul, algebraMap_smul]
          exact Submodule.smul_mem _ _ (hbB j)
        · have hpt := pt_mem_fibSub S τ (espan A) (Submodule.subset_span hx : x ∈ espan A)
          simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.starProjection_eq_self_iff.mpr hpt]
          rfl
      obtain ⟨n, hn⟩ := hTZ γ hγ
      refine ⟨n, ?_⟩
      rw [← hn]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have hU' : S.fibMap S' U' τ =
          ((τ.embedding (c : E)) • fibFun S τ (σ i)).smulRight (S'.pt τ (b j)) := by
        refine ext_pt S τ fun v => ?_
        rw [fibMap_pt', hU'v, pt_smul', LinearMap.smulRight_apply, LinearMap.smul_apply, fibFun_pt,
          map_mul, smul_eq_mul]
      have hcomp : γ τ ∘ₗ LinearMap.adjoint (T τ) =
          ((τ.embedding (c : E)) • (fibFun S τ (σ i) ∘ₗ LinearMap.adjoint (T τ))).smulRight
            (S'.pt τ (b j)) := by
        refine LinearMap.ext fun y => ?_
        have hy := hwA τ y
        simp only [γ, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          Submodule.starProjection_eq_self_iff.mpr hy, hU', LinearMap.smulRight_apply,
          LinearMap.smul_apply]
      change (τ.embedding (c : E) * fibFun S τ (σ i) (LinearMap.adjoint (T τ) (S'.pt τ (b j)))).re =
        hsInner S (T τ) (γ τ)
      unfold hsInner
      rw [re_trace_comp_adjoint (T τ) (γ τ), hcomp, LinearMap.trace_smulRight,
        LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    choose t ht using fun i j => exists_of_integral_pairing _ (hint i j)
    let U : S'.V →ₗ[E] S.V := ∑ j, (ρ j).smulRight (∑ i, t i j • a i)
    have hUv : ∀ v, U v = ∑ j, ρ j v • ∑ i, t i j • a i := fun v => by
      simp only [U, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine ⟨U, fun y hy => ?_, fun τ => ?_⟩
    · rw [hUv]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_smul]
      refine Submodule.subset_span ⟨ρ j y * t i j, ?_, a i, haA i, rfl⟩
      obtain ⟨o, ho⟩ := hρO j y hy
      rw [← ho, ← Algebra.smul_def]
      exact Submodule.smul_mem (_ : Submodule (𝓞 E) E) o (ht i j).2
    · have hUfib : S'.fibMap S U τ =
          ∑ j, (fibFun S' τ (ρ j)).smulRight (S.pt τ (∑ i, t i j • a i)) := by
        refine ext_pt S' τ fun v => ?_
        rw [fibMap_pt', hUv, pt_sum_smul', LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.smulRight_apply, fibFun_pt]
      have hwU : LinearMap.adjoint (T τ) = S'.fibMap S U τ ∘ₗ
          ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ) := by
        refine LinearMap.ext fun y => ?_
        have hperp := (S'.fibSub (espan B') τ).sub_starProjection_mem_orthogonal y
        have hPB := (S'.fibSub (espan B') τ).starProjection_apply_mem y
        have hsplit : y = (S'.fibSub (espan B') τ).starProjection y +
            (y - (S'.fibSub (espan B') τ).starProjection y) := by abel
        rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        conv_lhs => rw [hsplit, map_add, hwB τ _ hperp, add_zero]
        generalize (S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢
        have hx := dualBasis_at S' τ B' b ρ hidB hPB
        conv_lhs => rw [hx]
        rw [map_sum, hUfib, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smulRight_apply]
        congr 1
        have hA' := dualBasis_at S τ A a σ hidA (hwA τ (S'.pt τ (b j)))
        rw [hA', pt_sum_smul']
        exact Finset.sum_congr rfl fun i _ => by rw [(ht i j).1 τ]
      rw [← hwU, LinearMap.adjoint_adjoint]
  · rintro ⟨U, hU, hT⟩
    have hUE : ∀ y ∈ espan B', U y ∈ espan A := fun y hy =>
      map_espan_mem B' A U (fun x hx => mem_espan_of_smulIdeal _ A (hU x hx)) hy
    have hX : ∀ τ, (∀ y ∈ (S'.fibSub (espan B') τ)ᗮ, (S'.fibMap S U τ ∘ₗ
        ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y = 0) ∧
        ∀ y, (S'.fibMap S U τ ∘ₗ
          ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) y ∈
            S.fibSub (espan A) τ := by
      intro τ
      refine ⟨fun y hy => ?_, fun y => ?_⟩
      · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          (Submodule.starProjection_apply_eq_zero_iff _).mpr hy, map_zero]
      · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact fibMap_fibSub S' S τ U (espan B') (espan A) hUE
          ((S'.fibSub (espan B') τ).starProjection_apply_mem y)
    refine ⟨fun τ => ?_, fun γ hγ => ?_⟩
    · rw [hT τ]
      exact adjoint_maps _ _ _ (hX τ).1 (hX τ).2
    · obtain ⟨_, U', hU'A, hγpt⟩ := hγ
      let t : E := ∑ j, ρ j (U' (U (b j)))
      have ht : t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E := by
        refine Submodule.sum_mem (_ : Submodule (𝓞 E) E) fun j _ => ?_
        exact form_mem_of_smulIdeal _ B' (ρ j) (hρO j)
          (map_smulIdeal_mem _ A B' U' hU'A (hU (b j) (hbB j)))
      obtain ⟨n, hn⟩ := (mem_two_invDiff_iff t).mp ht 1
      refine ⟨n, ?_⟩
      have hU'E : ∀ y ∈ espan A, U' y ∈ espan B' := fun y hy =>
        map_espan_mem A B' U' (fun x hx => Submodule.subset_span (hU'A x hx)) hy
      have hτ : ∀ τ : InfinitePlace E, hsInner S (T τ) (γ τ) = (τ.embedding t).re := by
        intro τ
        unfold hsInner
        rw [re_trace_comp_adjoint, hT τ, LinearMap.adjoint_adjoint]
        have hγU : ∀ x ∈ S.fibSub (espan A) τ, γ τ x = S.fibMap S' U' τ x := fun x hx =>
          eqOn_fibSub S τ A (fun a ha => by rw [hγpt τ a ha, fibMap_pt']) hx
        have hcomp : γ τ ∘ₗ (S'.fibMap S U τ ∘ₗ
            ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)) =
            ∑ j, ((fibFun S' τ (ρ j)) ∘ₗ
              ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight
                (S'.pt τ (U' (U (b j)))) := by
          refine LinearMap.ext fun y => ?_
          simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.sum_apply,
            LinearMap.smulRight_apply]
          have hPB := (S'.fibSub (espan B') τ).starProjection_apply_mem y
          generalize (S'.fibSub (espan B') τ).starProjection y = x at hPB ⊢
          have hx := dualBasis_at S' τ B' b ρ hidB hPB
          conv_lhs => rw [hx]
          rw [map_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, map_smul, fibMap_pt',
            hγU _ (pt_mem_fibSub S τ (espan A) (hUE _ (Submodule.subset_span (hbB j)))),
            fibMap_pt']
        have hterm : ∀ j, LinearMap.trace ℂ (S'.FibSp τ) (((fibFun S' τ (ρ j)) ∘ₗ
            ((S'.fibSub (espan B') τ).starProjection : S'.FibSp τ →ₗ[ℂ] S'.FibSp τ)).smulRight
              (S'.pt τ (U' (U (b j))))) = τ.embedding (ρ j (U' (U (b j)))) := by
          intro j
          rw [LinearMap.trace_smulRight, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
            Submodule.starProjection_eq_self_iff.mpr (pt_mem_fibSub S' τ (espan B')
              (hU'E _ (hUE _ (Submodule.subset_span (hbB j))))), fibFun_pt]
        rw [hcomp, map_sum, Finset.sum_congr rfl fun j _ => hterm j, ← map_sum]
      unfold eucl
      rw [Finset.sum_congr rfl fun τ _ => hτ τ, sum_re_embedding]
      have hn' : Algebra.trace ℚ E t = 2 * n := by simpa using hn
      rw [hn']
      push_cast
      ring

end UnitaryReduction

end GroundTheory.Heights₂.Theta
