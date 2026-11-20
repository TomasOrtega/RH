import ReciprocityTheory.Chebotarev.Ucoord

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embZ_apply (α : 𝓞 E) : embZ α = mixedEmbedding E (α : E) := rfl

/- English proof (translation)
Introduce `a b h`. Conclude with `RingOfIntegers.coe_injective (mixedEmbedding_injective E h)`.
-/
theorem embZ_injective : Function.Injective (embZ (E := E)) := by
  intro a b h
  exact RingOfIntegers.coe_injective (mixedEmbedding_injective E h)

/- English proof (translation)
The claim follows from `Function.leftInverse_invFun embZ_injective α`.
-/
theorem preZ_embZ (α : 𝓞 E) : preZ (embZ α) = α :=
  Function.leftInverse_invFun embZ_injective α

/- English proof (translation)
Simplify using `only [latOf, Submodule.mem_map, Submodule.restrictScalars_mem]`.
-/
theorem mem_latOf {I : Ideal (𝓞 E)} {x : mixedSpace E} : x ∈ latOf I ↔ ∃ α ∈ I, embZ α = x := by
  simp only [latOf, Submodule.mem_map, Submodule.restrictScalars_mem]

/- English proof (translation)
The claim follows from `Submodule.map_mono (fun _ hx => h hx)`.
-/
theorem latOf_mono {I J : Ideal (𝓞 E)} (h : I ≤ J) : latOf I ≤ latOf J :=
  Submodule.map_mono (fun _ hx => h hx)

scoped instance discreteTopology_latOf (I : Ideal (𝓞 E)) : DiscreteTopology (latOf I) := by
  have hsub : ((latOf I : Set (mixedSpace E))) ⊆ (mixedEmbedding.integerLattice E : Set _) := by
    intro x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact ⟨α, rfl⟩
  exact DiscreteTopology.of_subset (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice E)) hsub

/- English proof (translation)
Establish `e : (I.restrictScalars ℤ) ≃ₗ[ℤ] latOf I` using `Submodule.equivMapOfInjective _ embZ_injective _`. Rewrite using `[← e.finrank_eq, Ideal.finrank_eq_finrank (RingOfIntegers.basis E) I hI, RingOfIntegers.rank]`.
-/
theorem finrank_latOf {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : Module.finrank ℤ (latOf I) = Module.finrank ℚ E := by
  have e : (I.restrictScalars ℤ) ≃ₗ[ℤ] latOf I := Submodule.equivMapOfInjective _ embZ_injective _
  rw [← e.finrank_eq, Ideal.finrank_eq_finrank (RingOfIntegers.basis E) I hI, RingOfIntegers.rank]

noncomputable def latEquiv (I : Ideal (𝓞 E)) : I ≃ latOf I :=
  Equiv.ofBijective (fun α => ⟨embZ (α : 𝓞 E), mem_latOf.mpr ⟨α, α.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (embZ_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨α, hα, h⟩ := mem_latOf.mp x.2
      exact ⟨⟨α, hα⟩, Subtype.ext h⟩⟩

/- English proof (translation)
The claim follows from `((latEquiv I).tsum_eq (fun x : latOf I => g x)).symm`.
-/
theorem tsum_latOf (I : Ideal (𝓞 E)) (g : mixedSpace E → ℂ) :
    ∑' x : latOf I, g x = ∑' α : I, g (embZ (α : 𝓞 E)) :=
  ((latEquiv I).tsum_eq (fun x : latOf I => g x)).symm

/- English proof (translation)
Rewrite using `[unitSMul_smul, embZ_apply, embZ_apply, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem unit_smul_embZ (u : (𝓞 E)ˣ) (α : 𝓞 E) : u • embZ α = embZ ((u : 𝓞 E) * α) := by
  rw [unitSMul_smul, embZ_apply, embZ_apply, ← map_mul]
  rfl

/- English proof (translation)
Rewrite using `[embZ_apply, norm_eq_norm, ← Algebra.coe_norm_int]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_embZ (α : 𝓞 E) : mixedEmbedding.norm (embZ α) = |((Algebra.norm ℤ α : ℤ) : ℝ)| := by
  rw [embZ_apply, norm_eq_norm, ← Algebra.coe_norm_int]
  push_cast
  rfl

section Sign

open NumberField.InfinitePlace

/- English proof (translation)
Use extensionality with `φ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `hφ`. Break down `InfinitePlace.mk_eq_iff.mp (hφ.trans (InfinitePlace.mk_embedding w).symm) with h | h` into its components or cases.

Conclude with `Or.inl h`. Conclude with `Or.inr (by rw [← h]; exact (star_involutive φ).symm)`. Introduce and unpack `(rfl | rfl)`. Conclude with `InfinitePlace.mk_embedding w`. Rewrite using `[InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem filter_infinitePlace_mk_eq_embedding_conjugate (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hφ
    rcases InfinitePlace.mk_eq_iff.mp (hφ.trans (InfinitePlace.mk_embedding w).symm) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; exact (star_involutive φ).symm)
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/- English proof (translation)
The claim follows from `map_prod (signHom : ℝ →*₀ SignType) f s`.
-/
theorem latOf_sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    SignType.sign (∏ i ∈ s, f i) = ∏ i ∈ s, SignType.sign (f i) :=
  map_prod (signHom : ℝ →*₀ SignType) f s

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ x`. Rewrite `h` using `[← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x) (fun _ => by simp [RingHom.equivRatAlgHom_apply])]`. Rewrite `h` using `[← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x), InfinitePlace.prod_eq_prod_mul_prod]`. Rewrite `h` using `[eq_ratCast]`.

Rewrite using `[Complex.ofReal_ratCast, h]`. Use `push_cast`. Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[filter_infinitePlace_mk_eq_embedding_conjugate, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton, Finset.prod_singleton, embedding_of_isReal_apply]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding`. Introduce `h'`. Conclude with `(not_isReal_iff_isComplex.mpr w.2) (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h'.symm))`. Rewrite using `[filter_infinitePlace_mk_eq_embedding_conjugate, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj, ← Complex.sq_norm, norm_embedding_eq]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem normQ_eq_prod_places (x : E) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 x) *
      ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 x) ^ 2 := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    InfinitePlace.prod_eq_prod_mul_prod] at h
  rw [eq_ratCast] at h
  rw [Complex.ofReal_ratCast, h]
  push_cast
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [filter_infinitePlace_mk_eq_embedding_conjugate, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      intro h'
      exact (not_isReal_iff_isComplex.mpr w.2) (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h'.symm))
    rw [filter_infinitePlace_mk_eq_embedding_conjugate, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
      ← Complex.sq_norm, norm_embedding_eq]
    push_cast
    rfl

/- English proof (translation)
Distinguish the cases in `hα : α = 0`. Simplify using `[hα]`. Establish `hx : (α : E) ≠ 0` using `by exact_mod_cast hα`. Establish `hN : ((Algebra.norm ℤ α : ℤ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 (α : E)) * ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 (α : E)) ^ 2`. Rewrite using `[← normQ_eq_prod_places, ← Algebra.coe_norm_int]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hsg : ((rsgn (embZ α) : ℤ) : ℝ) = ((SignType.sign ((Algebra.norm ℤ α : ℤ) : ℝ) : SignType) : ℝ)`. Rewrite using `[hN, sign_mul, latOf_sign_prod, latOf_sign_prod]`. Establish `hc : ∀ w : {w : InfinitePlace E // w.IsComplex}, SignType.sign ((w.1 (α : E)) ^ 2) = 1`.

Introduce `w`. Conclude with `sign_pos (pow_pos (pos_iff.mpr hx) 2)`. Simplify using `only [hc, Finset.prod_const_one, mul_one]`. Simplify using `only [rsgn, embZ_apply, mixedEmbedding_apply_isReal, Int.cast_prod]`. Simplify using `only [SignType.intCast_cast]`.

Conclude with `(map_prod (SignType.castHom : SignType →*₀ ℝ) _ _).symm`. Establish `key : ((rsgn (embZ α) * Algebra.norm ℤ α : ℤ) : ℝ) = ((|Algebra.norm ℤ α| : ℤ) : ℝ)`. Use `push_cast`. Rewrite using `[hsg, sign_mul_self]`. Conclude with `key` after adjusting the coercions.
-/
theorem rsgn_mul_norm (α : 𝓞 E) : rsgn (embZ α) * Algebra.norm ℤ α = |Algebra.norm ℤ α| := by
  by_cases hα : α = 0
  · simp [hα]
  have hx : (α : E) ≠ 0 := by exact_mod_cast hα
  have hN : ((Algebra.norm ℤ α : ℤ) : ℝ) = (∏ w : {w : InfinitePlace E // w.IsReal}, embedding_of_isReal w.2 (α : E)) *
      ∏ w : {w : InfinitePlace E // w.IsComplex}, (w.1 (α : E)) ^ 2 := by
    rw [← normQ_eq_prod_places, ← Algebra.coe_norm_int]
    push_cast
    rfl
  have hsg : ((rsgn (embZ α) : ℤ) : ℝ) = ((SignType.sign ((Algebra.norm ℤ α : ℤ) : ℝ) : SignType) : ℝ) := by
    rw [hN, sign_mul, latOf_sign_prod, latOf_sign_prod]
    have hc : ∀ w : {w : InfinitePlace E // w.IsComplex}, SignType.sign ((w.1 (α : E)) ^ 2) = 1 := by
      intro w
      exact sign_pos (pow_pos (pos_iff.mpr hx) 2)
    simp only [hc, Finset.prod_const_one, mul_one]
    simp only [rsgn, embZ_apply, mixedEmbedding_apply_isReal, Int.cast_prod]
    simp only [SignType.intCast_cast]
    exact (map_prod (SignType.castHom : SignType →*₀ ℝ) _ _).symm
  have key : ((rsgn (embZ α) * Algebra.norm ℤ α : ℤ) : ℝ) = ((|Algebra.norm ℤ α| : ℤ) : ℝ) := by
    push_cast
    rw [hsg, sign_mul_self]
  exact_mod_cast key

end Sign

end ReciprocityTheory.Cheb
