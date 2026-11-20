import Mathlib

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Polynomial

variable {O M₁ M₂ : Type*} [CommRing O] [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂]
  [Module O M₂]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem linearMap_mul_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g * h) x = g (h x) := rfl

/- English proof (translation)
Proceed by induction on `k generalizing y with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, pow_succ, linearMap_mul_apply, linearMap_mul_apply, ih, hf]`.
-/
theorem linearMap_pow_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (k : ℕ) (y : M₁) : f ((d₁ ^ k) y) = (d₂ ^ k) (f y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, linearMap_mul_apply, linearMap_mul_apply, ih, hf]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem linearMap_add_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g + h) x = g x + h x := rfl

/- English proof (translation)
Rewrite using `[aeval_monomial, linearMap_mul_apply]`. Use `first`. Consider the case `rw [Module.algebraMap_end_apply]`. Consider the case `simp`.
-/
private theorem aeval_end_monomial_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (n : ℕ) (a : O) (x : M) :
    aeval d (monomial n a) x = a • (d ^ n) x := by
  rw [aeval_monomial, linearMap_mul_apply]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

/- English proof (translation)
Use `Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add, map_add, linearMap_add_apply, linearMap_add_apply, map_add, hp, hq]`. Rewrite using `[aeval_end_monomial_apply, aeval_end_monomial_apply, map_smul, linearMap_pow_apply_comm_of_intertwine f d₁ d₂ hf]`.
-/
theorem linearMap_aeval_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (P : O[X]) (y : M₁) :
    f (aeval d₁ P y) = aeval d₂ P (f y) := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, map_add, linearMap_add_apply, linearMap_add_apply, map_add, hp, hq]
  · rw [aeval_end_monomial_apply, aeval_end_monomial_apply, map_smul, linearMap_pow_apply_comm_of_intertwine f d₁ d₂ hf]

/- English proof (translation)
Proceed by induction on `k generalizing y with`. Consider the case `zero => simpa using hy`. Consider the case `succ k ih`. Rewrite using `[pow_succ, linearMap_mul_apply]`. Conclude with `ih (hN y hy)`.
-/
private theorem pow_apply_mem_of_invariant' (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (k : ℕ) {y : M₁} (hy : y ∈ N) : (d ^ k) y ∈ N := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, linearMap_mul_apply]
    exact ih (hN y hy)

/- English proof (translation)
Use `Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add, linearMap_add_apply]`. Conclude with `N.add_mem hp hq`. Rewrite using `[aeval_end_monomial_apply]`. Conclude with `N.smul_mem a (pow_apply_mem_of_invariant' N d hN n hy)`.
-/
theorem aeval_apply_mem_of_invariant (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (P : O[X]) {y : M₁} (hy : y ∈ N) : aeval d P y ∈ N := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add, linearMap_add_apply]
    exact N.add_mem hp hq
  · rw [aeval_end_monomial_apply]
    exact N.smul_mem a (pow_apply_mem_of_invariant' N d hN n hy)

/- English proof (translation)
Rewrite using `[aeval_C]`. Use `first`. Consider the case `rw [Module.algebraMap_end_apply]`. Consider the case `simp`.
-/
private theorem aeval_end_C_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (a : O) (x : M) : aeval d (C a) x = a • x := by
  rw [aeval_C]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

/- English proof (translation)
Take `⟨A, B, hAB⟩ : ∃ A B : O[X], A * P₁ + B * P₂ = C e` from `by first`. Consider the case `exact Ideal.mem_span_pair.1 he`. Consider the case `simpa [smul_eq_mul] using Submodule.mem_span_pair.1 he`. Take `⟨y₁, hy₁, hfy₁⟩` from `h₁`. Take `⟨y₂, hy₂, hfy₂⟩` from `h₂`.

Use `⟨aeval d₁ A y₁ + aeval d₁ B y₂, N₁.add_mem (aeval_apply_mem_of_invariant N₁ d₁ hN A hy₁) (aeval_apply_mem_of_invariant N₁ d₁ hN B hy₂), ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_end_C_apply d₂ e x, ← hAB, map_add (aeval d₂), map_mul (aeval d₂), map_mul (aeval d₂), linearMap_add_apply, linearMap_mul_apply, linearMap_mul_apply, ← hfy₁, ← hfy₂, map_add f, linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf, linearMap_aeval_apply_comm_of_intertwine …`.
-/
theorem exists_mem_map_eq_smul (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (N₁ : Submodule O M₁) (hN : ∀ y ∈ N₁, d₁ y ∈ N₁)
    (P₁ P₂ : O[X]) (e : O) (he : C e ∈ Ideal.span ({P₁, P₂} : Set O[X])) (x : M₂)
    (h₁ : ∃ y ∈ N₁, f y = aeval d₂ P₁ x) (h₂ : ∃ y ∈ N₁, f y = aeval d₂ P₂ x) :
    ∃ y ∈ N₁, f y = e • x := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : O[X], A * P₁ + B * P₂ = C e := by
    first
      | exact Ideal.mem_span_pair.1 he
      | simpa [smul_eq_mul] using Submodule.mem_span_pair.1 he
  obtain ⟨y₁, hy₁, hfy₁⟩ := h₁
  obtain ⟨y₂, hy₂, hfy₂⟩ := h₂
  refine ⟨aeval d₁ A y₁ + aeval d₁ B y₂,
    N₁.add_mem (aeval_apply_mem_of_invariant N₁ d₁ hN A hy₁) (aeval_apply_mem_of_invariant N₁ d₁ hN B hy₂), ?_⟩
  rw [← aeval_end_C_apply d₂ e x, ← hAB, map_add (aeval d₂), map_mul (aeval d₂), map_mul (aeval d₂),
    linearMap_add_apply, linearMap_mul_apply, linearMap_mul_apply, ← hfy₁, ← hfy₂, map_add f,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
