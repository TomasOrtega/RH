import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d` from `⟨_, rfl⟩`. Take `⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m` from `⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩`. Establish `hm : 1 ≤ m` using `le_trans (Nat.le_add_left 1 _) hmK`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`.

Establish `hcon' : (h m : ℤ) ≤ (m : ℤ) * g m` using `by exact_mod_cast not_lt.mp hcon`. Establish `h1` using `(abs_le.mp (H1 m hm0)).1`. Establish `h2` using `(abs_le.mp (H2 m hm1)).2`. Rewrite `h1` using `[Nat.add_sub_cancel, Nat.factorial_succ]`. Move the coercions through the operations in `at h1`.

Establish `hM : (1 : ℤ) ≤ m` using `by exact_mod_cast hm`. Establish `hMK : (K : ℤ) * 2 ^ d + 1 ≤ m` using `by exact_mod_cast hmK`. Establish `hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d` using `by rw [hK]; push_cast; ring`. Generalize the expression as in `(m : ℤ) = M at *`. Establish `hF : (0 : ℤ) < d.factorial` using `by exact_mod_cast d.factorial_pos`.

Establish `hd : (0 : ℤ) ≤ d` using `by positivity`. Establish `hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d`. Break down `d with _ | e` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Nat.add_sub_cancel, pow_succ]`.

Establish `: (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith) d`.

Establish `hQ : 0 < M ^ d` using `by positivity`. Establish `e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m)` using `mul_le_mul_of_nonneg_left hcon' (by positivity)`. Establish `e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤ ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1)))` using `mul_le_mul_of_nonneg_left h2 (by positivity)`. Establish `e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤ ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d)` using `mul_le_mul_of_nonneg_left hA (by positivity)`. Establish `e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d)` using `mul_le_mul_of_nonneg_left hP (by positivity)`.

Establish `e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d` using `mul_le_mul_of_nonneg_right hMK hQ.le`. Establish `e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d)` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Establish `e7 : (K : ℤ) * (M + 1) ^ d = C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d)`. Rewrite using `[hKz]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[pow_succ' M d]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
