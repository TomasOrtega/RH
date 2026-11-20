import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.InfAdeleCM

variable {F : Type} [Field F] [NumberField F]

def ext (σ : F →+* ℂ) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) (InfinitePlace.mk σ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ext_apply (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := rfl

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp (continuous_apply (InfinitePlace.mk σ))`.
-/
theorem continuous_ext (σ : F →+* ℂ) : Continuous (ext σ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp
    (continuous_apply (InfinitePlace.mk σ))

/- English proof (translation)
Establish `h : (InfinitePlace.mk σ).embedding = σ` using `InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ)`. Rewrite using `[ext_apply, InfiniteAdeleRing.algebraMap_apply]`. Simplify using `[h]`.
-/
theorem ext_algebraMap [IsTotallyReal F] (σ : F →+* ℂ) (x : F) :
    ext σ (algebraMap F (InfiniteAdeleRing F) x) = σ x := by
  have h : (InfinitePlace.mk σ).embedding = σ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ)
  rw [ext_apply, InfiniteAdeleRing.algebraMap_apply]
  simp [h]

/- English proof (translation)
Rewrite using `[ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]`.
-/
theorem ext_eq_ofReal [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by
  rw [ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

/- English proof (translation)
Rewrite using `[ext_eq_ofReal, Complex.conj_ofReal]`.
-/
theorem conj_ext [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    starRingEnd ℂ (ext σ a) = ext σ a := by
  rw [ext_eq_ofReal, Complex.conj_ofReal]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra`. Set `f : InfiniteAdeleRing F →ₐ[F] ℂ` to `{ ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }`. Set `g : E →ₐ[F] ℂ` to `{ τ with commutes' := fun x => rfl }`. Use `⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Simplify using `[g]`. Establish `: (fun a : InfiniteAdeleRing F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =`. Use extensionality with `(τ.comp (algebraMap F E)) := by`. Use function extensionality and compare the values at `a`. Simplify using `[f]`.

Rewrite using `[this]`. Conclude with `continuous_ext _`.
-/
theorem exists_hom [IsTotallyReal F] (τ : E →+* ℂ) :
    ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧
      Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)) := by
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : InfiniteAdeleRing F →ₐ[F] ℂ :=
    { ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun x => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro x
    simp [g]
  · have : (fun a : InfiniteAdeleRing F =>
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =
        ext (τ.comp (algebraMap F E)) := by
      funext a
      simp [f]
    rw [this]
    exact continuous_ext _

/- English proof (translation)
Establish `: (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E))`. Use `(InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]`. Rewrite using `[← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Rewrite using `[← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem hom_tmul [IsTotallyReal F] (τ : E →+* ℂ) (θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ)
    (h1 : ∀ x, θ (1 ⊗ₜ x) = τ x) (h2 : Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)))
    (a : InfiniteAdeleRing F) (x : E) :
    θ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x := by
  have : (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_
    funext y
    simp only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]
    rw [← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, c y ≠ y := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc (AlgEquiv.ext h)`.

Establish `hcc : c (c y) = y` using `τ.injective (by rw [hτ, hτ, Complex.conj_conj])`. Establish `hδ : y - c y ≠ 0` using `sub_ne_zero.2 hy.symm`. Establish `hcδ : c (y - c y) = -(y - c y)` using `by rw [map_sub, hcc]; ring`. Use `⟨y - c y, hδ, hcδ, ?_⟩` and prove the remaining obligations. Generalize the expression as in `y - c y = δ at hδ hcδ`.

Establish `hli : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h'` using `congrArg c hst`. Establish `hsm : ∀ (p : F) (x : E), c (p • x) = p • c x` using `fun p x => by`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]`. Rewrite `h'` using `[map_add, hsm, hsm, map_one, hcδ, map_zero, smul_neg]`. Establish `ht : t • δ = 0`. Establish `: (2 : E) * (t • δ) = 0` using `by linear_combination hst - h'`. Simplify using `using this`.

Establish `ht' : t = 0` using `by simpa [hδ] using ht`. Use `⟨?_, ht'⟩` and prove the remaining obligations. Simplify `hst` using `[ht']`. Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank' (by simp [h2])`. Introduce `x`.

Establish `hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ])` using `hsp ▸ Submodule.mem_top`. Rewrite `hx` using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`. Take `⟨p, q, rfl⟩` from `hx`. Conclude with `⟨p, q, by simp [Algebra.smul_def]⟩`.
-/
theorem exists_delta (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) :
    ∃ δ : E, δ ≠ 0 ∧ c δ = -δ ∧ ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push_neg at h
    exact hc (AlgEquiv.ext h)
  have hcc : c (c y) = y := τ.injective (by rw [hτ, hτ, Complex.conj_conj])
  have hδ : y - c y ≠ 0 := sub_ne_zero.2 hy.symm
  have hcδ : c (y - c y) = -(y - c y) := by rw [map_sub, hcc]; ring
  refine ⟨y - c y, hδ, hcδ, ?_⟩
  generalize y - c y = δ at hδ hcδ
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg c hst
    have hsm : ∀ (p : F) (x : E), c (p • x) = p • c x := fun p x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]
    rw [map_add, hsm, hsm, map_one, hcδ, map_zero, smul_neg] at h'
    have ht : t • δ = 0 := by
      have : (2 : E) * (t • δ) = 0 := by linear_combination hst - h'
      simpa using this
    have ht' : t = 0 := by simpa [hδ] using ht
    refine ⟨?_, ht'⟩
    simpa [ht'] using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hx
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p, q, by simp [Algebra.smul_def]⟩

/- English proof (translation)
Establish `hp : ∀ p, τ (algebraMap F E p) = τ' (algebraMap F E p)` using `fun p => RingHom.congr_fun h p`. Take `⟨p, q, hpq⟩` from `hs (δ * δ)`. Establish `h'` using `congrArg c hpq`. Rewrite `h'` using `[map_mul, map_add, map_mul, hc, c.commutes, c.commutes]`. Establish `hsq : δ * δ = algebraMap F E p` using `by linear_combination (hpq + h') / 2`.

Establish `: τ δ * τ δ = τ' δ * τ' δ` using `by rw [← map_mul, ← map_mul, hsq, hp]`. Break down `mul_self_eq_mul_self_iff.1 this with e | e` into its components or cases. Use `left`. Use extensionality with `x`. Take `⟨p, q, rfl⟩` from `hs x`.

Simplify using `[hp, e]`. Use `right`. Use extensionality with `x`. Take `⟨p, q, rfl⟩` from `hs x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hτ]`.

Simplify using `[hp, e, hc]`.
-/
theorem eq_or_conj (c : E ≃ₐ[F] E) (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    {δ : E} (h0 : δ ≠ 0) (hc : c δ = -δ)
    (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ) (τ τ' : E →+* ℂ)
    (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E)) :
    τ = τ' ∨ τ = ComplexEmbedding.conjugate τ' := by
  have hp : ∀ p, τ (algebraMap F E p) = τ' (algebraMap F E p) := fun p => RingHom.congr_fun h p
  obtain ⟨p, q, hpq⟩ := hs (δ * δ)
  have h' := congrArg c hpq
  rw [map_mul, map_add, map_mul, hc, c.commutes, c.commutes] at h'
  have hsq : δ * δ = algebraMap F E p := by linear_combination (hpq + h') / 2
  have : τ δ * τ δ = τ' δ * τ' δ := by rw [← map_mul, ← map_mul, hsq, hp]
  rcases mul_self_eq_mul_self_iff.1 this with e | e
  · left
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    simp [hp, e]
  · right
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hτ]
    simp [hp, e, hc]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul a x`. Take `⟨p, q, rfl⟩` from `hs x`. Use `⟨p • a, q • a, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one]`. Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`. Conclude with `⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩`.
-/
theorem exists_decomp {δ : E} (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ)
    (z : InfiniteAdeleRing F ⊗[F] E) : ∃ a b : InfiniteAdeleRing F, z = a ⊗ₜ 1 + b ⊗ₜ δ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨p, q, rfl⟩ := hs x
    refine ⟨p • a, q • a, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

/- English proof (translation)
Rewrite using `[← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h, InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]`.
-/
theorem mk_eq_iff [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]

/- English proof (translation)
Establish `h : InfinitePlace.mk ((ComplexEmbedding.lift E w.embedding).comp (algebraMap F E)) = w`. Rewrite using `[ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]`. Distinguish the cases in `hm : ComplexEmbedding.lift E w.embedding ∈ Ψ`. Conclude with `⟨_, hm, h⟩`. Use `⟨ComplexEmbedding.conjugate (ComplexEmbedding.lift E w.embedding), ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Conclude with `hm ((hΨ _).2 hn)`. Rewrite using `[← h, ← InfinitePlace.mk_conjugate_eq]`. Use `congr 1`. Use extensionality with `x`.

Simplify using the standard rewrite rules.
-/
theorem exists_over [IsTotallyReal F] (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : InfinitePlace F) :
    ∃ τ ∈ Ψ, InfinitePlace.mk (τ.comp (algebraMap F E)) = w := by
  have h : InfinitePlace.mk ((ComplexEmbedding.lift E w.embedding).comp (algebraMap F E)) = w := by
    rw [ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]
  by_cases hm : ComplexEmbedding.lift E w.embedding ∈ Ψ
  · exact ⟨_, hm, h⟩
  · refine ⟨ComplexEmbedding.conjugate (ComplexEmbedding.lift E w.embedding), ?_, ?_⟩
    · by_contra hn
      exact hm ((hΨ _).2 hn)
    · rw [← h, ← InfinitePlace.mk_conjugate_eq]
      congr 1
      ext x
      simp

/- English proof (translation)
Take `⟨δ, h0, hcδ, hs⟩` from `exists_delta c h2 hc hτ`. Establish `hre : ∀ τ : E →+* ℂ, (τ δ).re = 0`. Introduce `τ`. Use `congrArg Complex.re (hτ τ δ)` as an intermediate fact. Rewrite `this` using `[hcδ, map_neg, Complex.neg_re, Complex.conj_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0`. Introduce `τ h`. Conclude with `h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))`. Set `r : ∀ w : InfinitePlace F, w.Completion →+* ℝ` to `fun w => InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)`.

Establish `hr : ∀ w, Function.Bijective (r w)` using `fun w => InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _`. Establish `hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) = ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))), r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩`. Introduce `τ a b`. Rewrite using `[map_add, hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]`. Use `choose t ht htw using exists_over (F := F) Ψ hΨ`. Prove the components needed by the constructor for the conclusion. Introduce `z z' hz`.

Take `⟨a, b, rfl⟩` from `exists_decomp hs z`. Take `⟨a', b', rfl⟩` from `exists_decomp hs z'`. Establish `key : ∀ w, a w = a' w ∧ b w = b' w`. Introduce `w`. Use `congrFun hz ⟨t w, ht w⟩` as an intermediate fact.

Simplify using `only [hval, Complex.mk.injEq] at this`. Rewrite `this` using `[htw w]`. Conclude with `⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩`. Establish `ha : a = a'` using `funext fun w => (key w).1`. Establish `hb : b = b'` using `funext fun w => (key w).2`.

Rewrite using `[ha, hb]`. Introduce `y choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)`. Use `⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Take `⟨τ, hτΨ⟩` from `τ`.

Establish `e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ`. Break down `eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e` into its components or cases. Conclude with `e`. Conclude with `absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)`. Use `hval τ a b` as an intermediate fact.

Simplify using `only [ha, hb, e] at this`. Use `this.trans ?_` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Conclude with `div_mul_cancel₀ _ (him τ)`.
-/
theorem bijective [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  obtain ⟨δ, h0, hcδ, hs⟩ := exists_delta c h2 hc hτ
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hτ τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ w : InfinitePlace F, w.Completion →+* ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have hr : ∀ w, Function.Bijective (r w) := fun w =>
    InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _
  have hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) =
      ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))),
        r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩ := by
    intro τ a b
    rw [map_add, hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]
  choose t ht htw using exists_over (F := F) Ψ hΨ
  constructor
  · intro z z' hz
    obtain ⟨a, b, rfl⟩ := exists_decomp hs z
    obtain ⟨a', b', rfl⟩ := exists_decomp hs z'
    have key : ∀ w, a w = a' w ∧ b w = b' w := by
      intro w
      have := congrFun hz ⟨t w, ht w⟩
      simp only [hval, Complex.mk.injEq] at this
      rw [htw w] at this
      exact ⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩
    have ha : a = a' := funext fun w => (key w).1
    have hb : b = b' := funext fun w => (key w).2
    rw [ha, hb]
  · intro y
    choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re
    choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)
    refine ⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩
    funext τ
    obtain ⟨τ, hτΨ⟩ := τ
    have e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ := by
      rcases eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e
      · exact e
      · exact absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)
    have := hval τ a b
    simp only [ha, hb, e] at this
    refine this.trans ?_
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ (him τ)

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc hF hτ`. Use `letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)`. Use `haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩`. Use `⟨exists_hom, fun θ hθ => ?_⟩` and prove the remaining obligations. Establish `hθ'` using `fun τ => hom_tmul τ (θ τ) (hθ τ).1 (hθ τ).2`.

Use `⟨fun τ => ?_, fun τ z => ?_, bijective c h2 hc hτ θ hθ'⟩` and prove the remaining obligations. Conclude with `IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing F) (θ τ) (hθ τ).2`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`.

Simplify using `only [sg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id, hθ', map_mul, conj_ext]`. Rewrite using `[← hτ]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem infAdele_tensor_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → IsTotallyReal F → (∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); (∀ τ : E →+* ℂ, ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) ∧ ∀ θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ), (∀ τ, (∀ x, θ τ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ τ (a ⊗ₜ (1 : E))) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sg (InfiniteAdeleRing F) c z) = starRingEnd ℂ (θ τ z)) ∧ ∀ Ψ : Set (E →+* ℂ), (∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  intro F E _ _ _ _ _ c h2 hc hF hτ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  refine ⟨exists_hom, fun θ hθ => ?_⟩
  have hθ' := fun τ => hom_tmul τ (θ τ) (hθ τ).1 (hθ τ).2
  refine ⟨fun τ => ?_, fun τ z => ?_, bijective c h2 hc hτ θ hθ'⟩
  · exact IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing F) (θ τ) (hθ τ).2
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [sg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id, hθ', map_mul, conj_ext]
      rw [← hτ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.InfAdeleCM
