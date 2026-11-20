import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Establish `hirr : Irreducible (X ^ p - C δ)` using `X_pow_sub_C_irreducible_of_prime h.prime h.nonpow`. Use `(minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C δ h.prime.ne_zero)).symm` and prove the remaining obligations. Simplify using `[h.pow]`.
-/
theorem IsKum.minpoly_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) : minpoly F θ = X ^ p - C δ := by
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime h.prime h.nonpow
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C δ h.prime.ne_zero)).symm
  simp [h.pow]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsKum.pow_apply {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]
    ring

/- English proof (translation)
Introduce `p F E _ _ _ _ ζ δ θ σ h`. Establish `hp` using `h.prime`. Establish `hp0 : p ≠ 0` using `hp.ne_zero`. Establish `: NeZero p` using `⟨hp0⟩`. Establish `hirr : Irreducible (X ^ p - C δ)` using `X_pow_sub_C_irreducible_of_prime hp h.nonpow`.

Establish `hζ : (primitiveRoots p F).Nonempty` using `⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩`. Establish `hinj : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Establish `hθ0 : θ ≠ 0`. Introduce `h0`. Establish `h1` using `h.pow`.

Rewrite `h1` using `[h0, zero_pow hp0, eq_comm, map_eq_zero]`. Conclude with `h.nonpow 0 (by rw [zero_pow hp0, h1])`. Establish `hsplit : IsSplittingField F E (X ^ p - C δ)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]`.

Conclude with `X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow`. Rewrite using `[eq_top_iff, ← h.gen]`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Rewrite using `[Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]`. Simplify using `[h.pow]`.

Establish `hfin : FiniteDimensional F E` using `IsSplittingField.finiteDimensional E (X ^ p - C δ)`. Establish `hrank : Module.finrank F E = p` using `finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)`. Establish `hgal : IsGalois F E` using `isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)`. Establish `hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂`. Introduce `τ₁ τ₂ hτ`.

Apply `AlgEquiv.coe_toAlgHom_injective` to reduce the goal to its premises. Apply `AlgHom.ext_of_adjoin_eq_top h.gen` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality.

Conclude with `hτ`. Establish `hσp : σ ^ p = 1` using `hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])`. Establish `hσ1 : σ ≠ 1`. Introduce `h1`. Establish `hc` using `h.conj`.

Rewrite `hc` using `[h1, AlgEquiv.one_apply]`. Establish `hz : algebraMap F E ζ = 1` using `mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])`. Conclude with `h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))`. Establish `hord : orderOf σ = p`. Use `Fact.mk hp` as an intermediate fact.

Conclude with `orderOf_eq_prime hσp hσ1`. Establish `hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ`. Introduce `τ`. Establish `hτp : (τ θ) ^ p = algebraMap F E δ` using `by rw [← map_pow, h.pow, AlgEquiv.commutes]`. Establish `hq : (τ θ / θ) ^ p = 1`.

Rewrite using `[div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]`. Take `⟨i, -, hi⟩` from `(h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq`. Rewrite using `[Subgroup.mem_zpowers_iff]`. Use `⟨i, hext _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]`.

Set `e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E` to `adjoinRootXPowSubCEquiv hζ hirr h.pow`. Use `⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩` and prove the remaining obligations. Introduce `L _ _ r hr`. Use `⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp e.symm.toAlgHom, ?_⟩` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root, AdjoinRoot.liftAlgHom_root]`.
-/
theorem kummer_galois : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by
  intro p F E _ _ _ _ ζ δ θ σ h
  have hp := h.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero p := ⟨hp0⟩
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime hp h.nonpow
  have hζ : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := h.pow
    rw [h0, zero_pow hp0, eq_comm, map_eq_zero] at h1
    exact h.nonpow 0 (by rw [zero_pow hp0, h1])
  have hsplit : IsSplittingField F E (X ^ p - C δ) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow
    · rw [eq_top_iff, ← h.gen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]
      simp [h.pow]
  have hfin : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ p - C δ)
  have hrank : Module.finrank F E = p :=
    finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hgal : IsGalois F E := isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top h.gen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτ
  have hσp : σ ^ p = 1 :=
    hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hc := h.conj
    rw [h1, AlgEquiv.one_apply] at hc
    have hz : algebraMap F E ζ = 1 := mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])
    exact h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))
  have hord : orderOf σ = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hσp hσ1
  have hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have hτp : (τ θ) ^ p = algebraMap F E δ := by rw [← map_pow, h.pow, AlgEquiv.commutes]
    have hq : (τ θ / θ) ^ p = 1 := by
      rw [div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]
    obtain ⟨i, -, hi⟩ := (h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i, hext _ _ ?_⟩
    rw [zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]
  let e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E := adjoinRootXPowSubCEquiv hζ hirr h.pow
  refine ⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩
  intro L _ _ r hr
  refine ⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp
    e.symm.toAlgHom, ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root,
    AdjoinRoot.liftAlgHom_root]

end GlobalTheory.CNorm
