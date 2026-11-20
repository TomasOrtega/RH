import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzd2.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

/- English proof (translation)
Introduce `a R _`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Establish `hi` using `i.isLt`. Set `k : Fin a` to `⟨a - 1 - (i : ℕ), by omega⟩`. Establish `hk : (k : ℕ) = a - 1 - (i : ℕ)` using `rfl`. Rewrite using `[Finset.sum_eq_single k]`. Establish `h1 : (i : ℕ) + (k : ℕ) + 1 = a` using `by omega`.

Rewrite using `[if_pos h1, if_pos rfl, ← mul_pow]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a)`. Introduce `h2`.

Apply `hb` to reduce the goal to its premises. Use `ext`. Use linear arithmetic over natural numbers and integers. Simplify using `[h1]`. Introduce `hk'`.

Conclude with `absurd (Finset.mem_univ k) hk'`. Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k _`. Distinguish the cases in `h1 : (i : ℕ) + (k : ℕ) + 1 = a`.

Establish `h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a)`. Introduce `h2`. Apply `h` to reduce the goal to its premises. Use `ext`. Use linear arithmetic over natural numbers and integers.

Simplify using `[h2]`. Simplify using `[h1]`.
-/
theorem UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd2.Phi a R * (UpperTheory.Reformulated.B.Yzd2.Phi a R).transpose = (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    have hi := i.isLt
    let k : Fin a := ⟨a - 1 - (i : ℕ), by omega⟩
    have hk : (k : ℕ) = a - 1 - (i : ℕ) := rfl
    rw [Finset.sum_eq_single k]
    · have h1 : (i : ℕ) + (k : ℕ) + 1 = a := by omega
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · intro b _ hb
      have h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a) := by
        intro h2
        apply hb
        ext
        omega
      simp [h1]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : (i : ℕ) + (k : ℕ) + 1 = a
    · have h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a) := by
        intro h2
        apply h
        ext
        omega
      simp [h2]
    · simp [h1]
