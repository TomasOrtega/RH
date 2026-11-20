import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with hm | hm` into its components or cases. Substitute `hm` using the available equality. Use `⟨0, fun x => ?_⟩` and prove the remaining obligations. Establish `: x = 0` using `Subsingleton.elim _ _`. Simplify using `[this]`.

Take `⟨c, hc⟩ : ∃ c : k, t (single (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ 1) = c` from `⟨_, rfl⟩`. Use `⟨c, fun x => ?_⟩` and prove the remaining obligations. Use `set o : Fin m := ⟨0, hm⟩`. Establish `key : ∀ a b : Fin m, t (single a b 1) = if a = b then c else 0`. Introduce `a b`.

Use `split_ifs with hab`. Substitute `hab` using the available equality. Establish `h1 : single a a (1 : k) = single a o 1 * single o a 1`. Rewrite using `[single_mul_single_same, mul_one]`. Establish `h2 : single o o (1 : k) = single o a 1 * single a o 1`.

Rewrite using `[single_mul_single_same, mul_one]`. Rewrite using `[h1, ht, ← h2, hc]`. Establish `h1 : single a b (1 : k) = single a a 1 * single a b 1`. Rewrite using `[single_mul_single_same, mul_one]`. Establish `h2 : single a b (1 : k) * single a a 1 = 0` using `single_mul_single_of_ne (1 : k) a b a (Ne.symm hab) 1`.

Rewrite using `[h1, ht, h2, map_zero]`. Establish `hx : x = ∑ a, ∑ b, x a b • single a b (1 : k)` using `by conv_lhs => rw [matrix_eq_sum_single x]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[smul_single, smul_eq_mul, mul_one]`. Use `conv_lhs => rw [hx]`.

Simplify using `only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[trace, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem linearForm_matrix_eq_smul_trace_of_comm (k : Type) [Field k] (m : ℕ)
    (t : Matrix (Fin m) (Fin m) k →ₗ[k] k) (ht : ∀ x y, t (x * y) = t (y * x)) :
    ∃ c : k, ∀ x, t x = c * x.trace := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : k, t (single (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ 1) = c := ⟨_, rfl⟩
    refine ⟨c, fun x => ?_⟩
    set o : Fin m := ⟨0, hm⟩
    have key : ∀ a b : Fin m, t (single a b 1) = if a = b then c else 0 := by
      intro a b
      split_ifs with hab
      · subst hab
        have h1 : single a a (1 : k) = single a o 1 * single o a 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single o o (1 : k) = single o a 1 * single a o 1 := by
          rw [single_mul_single_same, mul_one]
        rw [h1, ht, ← h2, hc]
      · have h1 : single a b (1 : k) = single a a 1 * single a b 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single a b (1 : k) * single a a 1 = 0 :=
          single_mul_single_of_ne (1 : k) a b a (Ne.symm hab) 1
        rw [h1, ht, h2, map_zero]
    have hx : x = ∑ a, ∑ b, x a b • single a b (1 : k) := by
      conv_lhs => rw [matrix_eq_sum_single x]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]

/- English proof (translation)
Introduce `k _ N n τ hτ`. Establish `h : ∀ i, ∃ c : k, ∀ A, (τ ∘ₗ LinearMap.single k (fun i => Matrix (Fin (n i)) (Fin (n i)) k) i) A = c * A.trace`. Introduce `i`. Use `linearForm_matrix_eq_smul_trace_of_comm k (n i) _ fun A B => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]`.

Rewrite using `[Pi.single_mul, Pi.single_mul, hτ]`. Use `choose c hc using h`. Use `⟨c, fun x => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Finset.univ_sum_single x]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `hc i (x i)` as an intermediate fact. Simplify using `using this`.
-/
theorem centralLinearForm_pi_matrix_eq_sum_trace :
    ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ)
      (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k),
      (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  intro k _ N n τ hτ
  have h : ∀ i, ∃ c : k, ∀ A, (τ ∘ₗ LinearMap.single k (fun i => Matrix (Fin (n i)) (Fin (n i)) k) i) A
      = c * A.trace := by
    intro i
    refine linearForm_matrix_eq_smul_trace_of_comm k (n i) _ fun A B => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Pi.single_mul, Pi.single_mul, hτ]
  choose c hc using h
  refine ⟨c, fun x => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hc i (x i)
  simpa using this

end GlobalTheory
