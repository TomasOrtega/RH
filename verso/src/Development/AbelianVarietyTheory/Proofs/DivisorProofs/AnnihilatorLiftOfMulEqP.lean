import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p O _ Λ _ k _ π hpk hp2 M _ _ _ _ htor N _ _ f hf hker ϖ z hϖz n hn`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp hϖz`. Establish `hL : ∀ (c : Λ) (m : M), c • m = (c ⊗ₜ[ℤ] (1 : O)) • m`. Introduce `c m`. Rewrite using `[← smul_one_smul (Λ ⊗[ℤ] O) c m]`.

Use `congr 1`. Rewrite using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hp2M : ∀ m : M, ((p : Λ) ^ 2) • m = 0` using `by intro m; rw [hp2, zero_smul]`. Establish `hpz : ∀ m : M, (p : Λ) • m = ((1 : Λ) ⊗ₜ[ℤ] z) • ((1 : Λ) ⊗ₜ[ℤ] ϖ) • m`. Introduce `m`.

Rewrite using `[smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm z ϖ]`. Establish `: ϖ * z = (p : O) + y * (p : O) ^ 2` using `by linear_combination -hy`. Rewrite using `[this, TensorProduct.tmul_add, add_smul]`. Establish `h1 : ((1 : Λ) ⊗ₜ[ℤ] (p : O)) = ((p : Λ) ⊗ₜ[ℤ] (1 : O))`. Establish `e1 : (p : O) = p • (1 : O)` using `by simp`.

Establish `e2 : (p : Λ) = p • (1 : Λ)` using `by simp`. Rewrite using `[e1, e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Establish `h2 : ((1 : Λ) ⊗ₜ[ℤ] (y * (p : O) ^ 2)) = ((p : Λ) ^ 2) • ((1 : Λ) ⊗ₜ[ℤ] y)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[show (y * (p : O) ^ 2) = ((p ^ 2 : ℕ) : ℤ) • y by push_cast; simp [zsmul_eq_mul]; ring]`.

Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Use `congr 1`. Use `push_cast`. Simplify using `[zsmul_eq_mul]`. Rewrite using `[h1, h2, ← hL, smul_assoc, hp2M, add_zero]`.

Establish `hσp : ∀ m : M, f ((p : Λ) • m) = 0`. Introduce `m`. Rewrite using `[hL, f.map_smulₛₗ]`. Establish `: (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((p : Λ) ⊗ₜ[ℤ] (1 : O)) = 0`. Simplify using `[Algebra.TensorProduct.map_tmul, hpk]`.

Rewrite using `[this, zero_smul]`. Establish `hf0 : ∀ m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M), f m = 0`. Introduce `m hm`. Rewrite `hm` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨b, -, rfl⟩` from `hm`.

Conclude with `hσp b`. Establish `hσϖ : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] ϖ) = (1 : k) ⊗ₜ[ℤ] ϖ`. Simplify using `[Algebra.TensorProduct.map_tmul]`. Establish `hσz : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] z) = (1 : k) ⊗ₜ[ℤ] z`. Simplify using `[Algebra.TensorProduct.map_tmul]`.

Take `⟨m, rfl⟩` from `hf n`. Establish `h1 : f (((1 : Λ) ⊗ₜ[ℤ] ϖ) • m) = 0` using `by rw [f.map_smulₛₗ, hσϖ]; exact hn`. Establish `h2` using `hker _ h1`. Rewrite `h2` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨m', -, hm'⟩` from `h2`.

Establish `h3 : ((1 : Λ) ⊗ₜ[ℤ] ϖ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0`. Rewrite using `[smul_sub, ← hm', smul_smul, mul_comm ((1 : Λ) ⊗ₜ[ℤ] ϖ), ← smul_smul, ← hpz, sub_self]`. Establish `h4 : (p : Λ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0`. Rewrite using `[hpz, h3, smul_zero]`. Establish `h5` using `hf0 _ (htor _ h4)`.

Establish `hn' : f m = ((1 : k) ⊗ₜ[ℤ] z) • f m'`. Rewrite `h5` using `[map_sub, f.map_smulₛₗ, hσz, sub_eq_zero]`. Conclude with `h5`. Rewrite using `[hn']`. Apply `Submodule.smul_mem_smul _ Submodule.mem_top` to reduce the goal to its premises.

Apply `Ideal.subset_span` to reduce the goal to its premises. Use `show ((1 : k) ⊗ₜ[ℤ] ϖ) * ((1 : k) ⊗ₜ[ℤ] z) = 0`. Establish `hw : ϖ * z = ((p : ℤ) • (1 + (p : O) * y))` using `by rw [zsmul_eq_mul]; push_cast; linear_combination -hy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, hw, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]`. Use `push_cast`.

Rewrite using `[hpk, TensorProduct.zero_tmul]`.
-/
theorem annihilator_lift_of_mul_eq_p : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  intro p O _ Λ _ k _ π hpk hp2 M _ _ _ _ htor N _ _ f hf hker ϖ z hϖz n hn
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hϖz

  have hL : ∀ (c : Λ) (m : M), c • m = (c ⊗ₜ[ℤ] (1 : O)) • m := by
    intro c m
    rw [← smul_one_smul (Λ ⊗[ℤ] O) c m]
    congr 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  have hp2M : ∀ m : M, ((p : Λ) ^ 2) • m = 0 := by intro m; rw [hp2, zero_smul]

  have hpz : ∀ m : M, (p : Λ) • m = ((1 : Λ) ⊗ₜ[ℤ] z) • ((1 : Λ) ⊗ₜ[ℤ] ϖ) • m := by
    intro m
    rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm z ϖ]
    have : ϖ * z = (p : O) + y * (p : O) ^ 2 := by linear_combination -hy
    rw [this, TensorProduct.tmul_add, add_smul]
    have h1 : ((1 : Λ) ⊗ₜ[ℤ] (p : O)) = ((p : Λ) ⊗ₜ[ℤ] (1 : O)) := by
      have e1 : (p : O) = p • (1 : O) := by simp
      have e2 : (p : Λ) = p • (1 : Λ) := by simp
      rw [e1, e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : ((1 : Λ) ⊗ₜ[ℤ] (y * (p : O) ^ 2)) = ((p : Λ) ^ 2) • ((1 : Λ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [show (y * (p : O) ^ 2) = ((p ^ 2 : ℕ) : ℤ) • y by push_cast; simp [zsmul_eq_mul]; ring]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      push_cast; simp [zsmul_eq_mul]
    rw [h1, h2, ← hL, smul_assoc, hp2M, add_zero]

  have hσp : ∀ m : M, f ((p : Λ) • m) = 0 := by
    intro m
    rw [hL, f.map_smulₛₗ]
    have : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((p : Λ) ⊗ₜ[ℤ] (1 : O)) = 0 := by
      simp [Algebra.TensorProduct.map_tmul, hpk]
    rw [this, zero_smul]
  have hf0 : ∀ m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M), f m = 0 := by
    intro m hm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    exact hσp b
  have hσϖ : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] ϖ) = (1 : k) ⊗ₜ[ℤ] ϖ := by
    simp [Algebra.TensorProduct.map_tmul]
  have hσz : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] z) = (1 : k) ⊗ₜ[ℤ] z := by
    simp [Algebra.TensorProduct.map_tmul]
  obtain ⟨m, rfl⟩ := hf n
  have h1 : f (((1 : Λ) ⊗ₜ[ℤ] ϖ) • m) = 0 := by rw [f.map_smulₛₗ, hσϖ]; exact hn
  have h2 := hker _ h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨m', -, hm'⟩ := h2
  have h3 : ((1 : Λ) ⊗ₜ[ℤ] ϖ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [smul_sub, ← hm', smul_smul, mul_comm ((1 : Λ) ⊗ₜ[ℤ] ϖ), ← smul_smul, ← hpz, sub_self]
  have h4 : (p : Λ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [hpz, h3, smul_zero]
  have h5 := hf0 _ (htor _ h4)
  have hn' : f m = ((1 : k) ⊗ₜ[ℤ] z) • f m' := by
    rw [map_sub, f.map_smulₛₗ, hσz, sub_eq_zero] at h5; exact h5
  rw [hn']
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.subset_span
  show ((1 : k) ⊗ₜ[ℤ] ϖ) * ((1 : k) ⊗ₜ[ℤ] z) = 0
  have hw : ϖ * z = ((p : ℤ) • (1 + (p : O) * y)) := by rw [zsmul_eq_mul]; push_cast; linear_combination -hy
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hw, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  push_cast
  rw [hpk, TensorProduct.zero_tmul]

end GlobalTheory
