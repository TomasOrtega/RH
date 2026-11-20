import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Use `Subalgebra.isSimpleOrder_of_finrank h2` as an intermediate fact. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h` into its components or cases. Establish `hm : e ∈ AlgHom.equalizer σ (AlgHom.id F E)`. Rewrite using `[AlgHom.mem_equalizer]`. Simplify using `using he`.

Rewrite `hm` using `[h]`. Conclude with `Algebra.mem_bot.mp hm`. It suffices to derive a contradiction. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Establish `hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `by rw [h]; trivial`. Rewrite `hm` using `[AlgHom.mem_equalizer]`. Establish `h1` using `hσ τ x`.

Rewrite `h1` using `[hm]`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `h1.symm`.
-/
theorem mem_range_algebraMap_of_conj_fixed (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : E) (he : σ e = e) :
    ∃ c : F, algebraMap F E c = e := by
  have := Subalgebra.isSimpleOrder_of_finrank h2
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [AlgHom.mem_equalizer]; simpa using he
    rw [h] at hm
    exact Algebra.mem_bot.mp hm
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    rw [AlgHom.mem_equalizer] at hm
    have h1 := hσ τ x
    rw [hm] at h1
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1.symm

/- English proof (translation)
Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hσ, hσ, star_star]`.

Use `set φ := Algebra.TensorProduct.map (AlgHom.id F R) σ with hφ`. Establish `key : ∀ y z : R ⊗[F] E, ∃ n : R, y * φ z + z * φ y = algebraMap R (R ⊗[F] E) n`. Introduce `y z`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add y₁ y₂ h₁ h₂`. Take `⟨n₁, h₁⟩` from `h₁`. Take `⟨n₂, h₂⟩` from `h₂`. Conclude with `⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩`. Consider the case `tmul a e`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add z₁ z₂ h₁ h₂`. Take `⟨n₁, h₁⟩` from `h₁`. Take `⟨n₂, h₂⟩` from `h₂`.

Conclude with `⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩`. Consider the case `tmul b f`. Take `⟨c, hc⟩` from `mem_range_algebraMap_of_conj_fixed F E σ hE h2 hσ (e * σ f + f * σ e) (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)`. Use `⟨c • (a * b), ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, AlgHom.id_apply, AlgHom.id_apply, mul_comm b a, ← TensorProduct.tmul_add, ← hc, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMa …`.

Take `⟨n, hn⟩` from `key y y`. Use `⟨algebraMap F R (1 / 2) * n, ?_⟩` and prove the remaining obligations. Establish `h : algebraMap F R (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul]`. Evaluate the numerical expressions.

Establish `h' : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h, map_one]`. Rewrite using `[map_mul, ← hn, ← two_mul, ← mul_assoc, h', one_mul]`.
-/
theorem exists_mul_conj_eq_algebraMap (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    ∃ n : R, y * Algebra.TensorProduct.map (AlgHom.id F R) σ y = algebraMap R (R ⊗[F] E) n := by
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ, hσ, star_star]
  set φ := Algebra.TensorProduct.map (AlgHom.id F R) σ with hφ
  have key : ∀ y z : R ⊗[F] E, ∃ n : R, y * φ z + z * φ y = algebraMap R (R ⊗[F] E) n := by
    intro y z
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨n₁, h₁⟩ := h₁
      obtain ⟨n₂, h₂⟩ := h₂
      exact ⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩
    | tmul a e =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        exact ⟨n₁ + n₂, by rw [map_add, map_add, ← h₁, ← h₂]; ring⟩
      | tmul b f =>
        obtain ⟨c, hc⟩ := mem_range_algebraMap_of_conj_fixed F E σ hE h2 hσ
          (e * σ f + f * σ e) (by rw [map_add, map_mul, map_mul, hinv, hinv]; ring)
        refine ⟨c • (a * b), ?_⟩
        rw [hφ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          AlgHom.id_apply, AlgHom.id_apply, mul_comm b a, ← TensorProduct.tmul_add, ← hc,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨n, hn⟩ := key y y
  refine ⟨algebraMap F R (1 / 2) * n, ?_⟩
  have h : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
  have h' : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h, map_one]
  rw [map_mul, ← hn, ← two_mul, ← mul_assoc, h', one_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ hE h2 hσ R _ _ x`. Take `⟨n, hn⟩` from `exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R (x : R ⊗[F] E)`. Take `⟨m, hm⟩` from `exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R ((x⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)`. Establish `hinj : Function.Injective (algebraMap R (R ⊗[F] E))` using `Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap F E).injective`. Establish `hnm : n * m = 1`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, ← hn, ← hm, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, mul_one]`. Conclude with `⟨⟨n, m, hnm, by rw [mul_comm, hnm]⟩, hn⟩`.
-/
theorem exists_unit_mul_conj_eq_algebraMap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → ∀ (R : Type) [CommRing R] [Algebra F R] (x : (R ⊗[F] E)ˣ), ∃ n : Rˣ, (x : R ⊗[F] E) * Algebra.TensorProduct.map (AlgHom.id F R) σ (x : R ⊗[F] E) = algebraMap R (R ⊗[F] E) n := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ R _ _ x
  obtain ⟨n, hn⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R (x : R ⊗[F] E)
  obtain ⟨m, hm⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R ((x⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap F E).injective
  have hnm : n * m = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hn, ← hm, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  exact ⟨⟨n, m, hnm, by rw [mul_comm, hnm]⟩, hn⟩

end GlobalTheory
