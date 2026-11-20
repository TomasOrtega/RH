import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.Arith.DedekindDescent

/- English proof (translation)
Set `_ : Algebra F ℂ` to `σ.toAlgebra`. Establish `: CharZero F` using `⟨fun a b hab => Nat.cast_injective (R := ℂ) (by`. Use `congrArg σ hab` as an intermediate fact. Simplify `this)⟩` using `only [map_natCast]`. Establish `key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0`.

Introduce `y`. Establish `htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y)` using `fun k => trace_eq_sum_embeddings ℂ (x := x k * y)`. Simplify using `only [htr, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun φ _ => ?_` and prove the remaining obligations.

Establish `hφ` using `h (φ : K →+* ℂ) φ.comp_algebraMap`. Establish `hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.coe_toRingHom]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, hφ, mul_zero]`. Use function extensionality and compare the values at `k0`. Assume the negation of the conclusion as `hne`. Establish `h0` using `congrFun (hb _ (key (x k0)⁻¹)) k0`.

Simplify using `only [Pi.zero_apply] at h0 hne`. Rewrite `h0` using `[mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, Nat.cast_eq_zero]`. Conclude with `(Module.finrank_pos (R := F) (M := K)).ne' h0`.
-/
theorem single_ext (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : F →+* ℂ) {κ : Type} [Fintype κ] (b : κ → ℂ)
    (hb : ∀ c : κ → F, ∑ k, σ (c k) * b k = 0 → c = 0) (x : κ → K)
    (h : ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∑ k, b k * τ (x k) = 0) : x = 0 := by
  let _ : Algebra F ℂ := σ.toAlgebra
  have : CharZero F := ⟨fun a b hab => Nat.cast_injective (R := ℂ) (by
    have := congrArg σ hab
    simpa only [map_natCast] using this)⟩
  have key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0 := by
    intro y
    have htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y) :=
      fun k => trace_eq_sum_embeddings ℂ (x := x k * y)
    simp only [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have hφ := h (φ : K →+* ℂ) φ.comp_algebraMap
    have hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, AlgHom.coe_toRingHom]
      ring
    rw [hsplit, hφ, mul_zero]
  funext k0
  by_contra hne
  have h0 := congrFun (hb _ (key (x k0)⁻¹)) k0
  simp only [Pi.zero_apply] at h0 hne
  rw [mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_one, Nat.cast_eq_zero] at h0
  exact (Module.finrank_pos (R := F) (M := K)).ne' h0

/- English proof (translation)
Introduce `F _ σ J K _ _ _ ι _ v hv d hd`. Set `_ : Algebra F ℂ` to `σ.toAlgebra`. Set `S` to `Submodule.span F (Set.range d)`. Establish `: FiniteDimensional F S` using `FiniteDimensional.span_of_finite F (Set.finite_range d)`. Set `B` to `Module.finBasis F S`.

Establish `hmem : ∀ l, d l ∈ S` using `fun l => Submodule.subset_span ⟨l, rfl⟩`. Establish `hval : ∀ e : Fin (Module.finrank F S) → F, ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ)`. Introduce `e`. Simplify using `only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Establish `hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ)`.

Introduce `l`. Rewrite using `[← hval]`. Conclude with `(congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm`. Establish `hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0`. Introduce `e he`.

Establish `h1 : ∑ k, e k • B k = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hval, he]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `k`.

Conclude with `Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k`. Establish `hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0`. Introduce `j`. Establish `hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ → ∀ a, τ (algebraMap F (K j) a) = σ a` using `fun τ hτ a => by rw [← hτ]; rfl`. Use `single_ext F (K j) σ (fun k => (B k : ℂ)) hbind (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by` as an intermediate fact.

Use `Eq.trans ?_ (hd j τ hτ)` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, hτ' τ hτ]`. Rewrite using `[Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)`. Introduce `k`. Conclude with `congrFun this k`. Establish `hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0` using `fun k => hv _ fun j => hx j k`. Use function extensionality and compare the values at `l`.

Rewrite using `[hdc l, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Use `congrFun (hc0 k) l` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Rewrite using `[this, map_zero, zero_mul]`.
-/
theorem linIndep_descent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (J : Type) (K : J → Type) [∀ j, Field (K j)] [∀ j, Algebra F (K j)] [∀ j, FiniteDimensional F (K j)] (ι : Type) [Fintype ι] (v : ι → ∀ j, K j), (∀ a : ι → F, (∀ j, ∑ l, algebraMap F (K j) (a l) * v l j = 0) → a = 0) → ∀ d : ι → ℂ, (∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ → ∑ l, d l * τ (v l j) = 0) → d = 0 := by
  intro F _ σ J K _ _ _ ι _ v hv d hd
  let _ : Algebra F ℂ := σ.toAlgebra
  let S := Submodule.span F (Set.range d)
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range d)
  let B := Module.finBasis F S
  have hmem : ∀ l, d l ∈ S := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hval : ∀ e : Fin (Module.finrank F S) → F,
      ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ) := by
    intro e
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ) := by
    intro l
    rw [← hval]
    exact (congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm
  have hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0 := by
    intro e he
    have h1 : ∑ k, e k • B k = 0 := by
      apply Subtype.ext
      rw [hval, he]
      rfl
    funext k
    exact Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k
  have hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0 := by
    intro j
    have hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ →
        ∀ a, τ (algebraMap F (K j) a) = σ a := fun τ hτ a => by rw [← hτ]; rfl
    have := single_ext F (K j) σ (fun k => (B k : ℂ)) hbind
      (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by
        refine Eq.trans ?_ (hd j τ hτ)
        simp only [map_sum, map_mul, hτ' τ hτ]
        rw [Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    intro k
    exact congrFun this k
  have hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0 := fun k => hv _ fun j => hx j k
  funext l
  rw [hdc l, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrFun (hc0 k) l
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, zero_mul]

end GlobalTheory.CompanionTheory.Arith.DedekindDescent
