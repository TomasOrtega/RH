import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `R _ n u h1 h2`. Establish `key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m → ((List.ofFn u).take m).prod i j = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ i j hj`.

Conclude with `absurd hj (Nat.not_lt_zero _)`. Consider the case `succ m ih`. Introduce `hm i j hj`. Establish `hlen : m < (List.ofFn u).length`. Rewrite using `[List.length_ofFn]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[List.prod_take_succ _ _ hlen, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l.val < m`. Rewrite using `[ih (by omega) i l hl, zero_mul]`.

Establish `hu : (List.ofFn u)[m] = u ⟨m, by omega⟩`. Simplify using the standard rewrite rules. Rewrite using `[hu]`. Distinguish the cases in `hjl : j < l`. Rewrite using `[h1 _ _ _ hjl, mul_zero]`.

Establish `hjl' : l.val ≤ j.val` using `Fin.le_def.mp (not_lt.mp hjl)`. Establish `e1 : l = ⟨m, by omega⟩` using `Fin.ext (by simp; omega)`. Establish `e2 : j = ⟨m, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e1, e2, h2, mul_zero]`. Use extensionality with `i j`.

Use `key n le_rfl i j j.isLt` as an intermediate fact. Rewrite `this` using `[List.take_of_length_le (by simp)]`. Simplify using `using this`.
-/
theorem UpperTheory.V.AlgebraTools.tri_prod_zero :
    ∀ {R : Type} [CommRing R] {n : ℕ} (u : Fin n → Matrix (Fin n) (Fin n) R), (∀ k i j, j < i → u k i j = 0) → (∀ k, u k k k = 0) → (List.ofFn u).prod = 0 := by
  intro R _ n u h1 h2
  have key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m →
      ((List.ofFn u).take m).prod i j = 0 := by
    intro m
    induction m with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm i j hj
      have hlen : m < (List.ofFn u).length := by
        rw [List.length_ofFn]; omega
      rw [List.prod_take_succ _ _ hlen, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < m
      · rw [ih (by omega) i l hl, zero_mul]
      · have hu : (List.ofFn u)[m] = u ⟨m, by omega⟩ := by
          simp
        rw [hu]
        by_cases hjl : j < l
        · rw [h1 _ _ _ hjl, mul_zero]
        · have hjl' : l.val ≤ j.val := Fin.le_def.mp (not_lt.mp hjl)
          have e1 : l = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e1, e2, h2, mul_zero]
  ext i j
  have := key n le_rfl i j j.isLt
  rw [List.take_of_length_le (by simp)] at this
  simpa using this
