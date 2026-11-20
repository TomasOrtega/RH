import Formalism.LogFactorialBounds.LocalFactorSplitDv
import Mathlib

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

/- English proof (translation)
Break down `Nat.lt_or_ge n p with h | h` into its components or cases. Rewrite using `[Nat.div_eq_of_lt h]`. Conclude with `Nat.zero_le _`. Rewrite using `[Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]`. Establish `hpos : 0 < Nat.log p n` using `Nat.log_pos hp.one_lt h`.

Establish `h1 : 1 ∈ Finset.Ico 1 (Nat.succ (Nat.log p n))` using `Finset.mem_Ico.2 ⟨le_rfl, by omega⟩`. Use `Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1` as an intermediate fact. Simplify using `using this`.
-/
lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rcases Nat.lt_or_ge n p with h | h
  · rw [Nat.div_eq_of_lt h]
    exact Nat.zero_le _
  · rw [Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]
    have hpos : 0 < Nat.log p n := Nat.log_pos hp.one_lt h
    have h1 : 1 ∈ Finset.Ico 1 (Nat.succ (Nat.log p n)) :=
      Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

/- English proof (translation)
Establish `key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ^ (n / p) ∣ n.factorial`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using the standard rewrite rules.

Introduce `a s ha ih h`. Rewrite using `[Finset.prod_insert ha]`. Establish `hs` using `ih (fun p hp => h p (Finset.mem_insert_of_mem hp))`. Establish `haP` using `h a (Finset.mem_insert_self a s)`. Establish `hcop : Nat.Coprime (a ^ (n / a)) (∏ p ∈ s, p ^ (n / p))`.

Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Apply `Nat.Coprime.prod_right` to reduce the goal to its premises. Introduce `p hp`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Conclude with `(Nat.coprime_primes haP (h p (Finset.mem_insert_of_mem hp))).2 (fun e => ha (by rw [e]; exact hp))`.

Conclude with `hcop.mul_dvd_of_dvd_of_dvd ((haP.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n)).2 (div_le_factorization_factorial haP n)) hs`. Establish `hd : ∏ p ∈ Nat.primesLE n, p ^ (n / p) ∣ n.factorial` using `key _ (fun p hp => (Nat.mem_primesLE.1 hp).2)`. Establish `hle : ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) ≤ (n.factorial : ℕ)`. Conclude with `Nat.le_of_dvd (Nat.factorial_pos n) hd` after adjusting the coercions. Establish `hpos : (0 : ℝ) < ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ)`.

Conclude with `Finset.prod_pos (fun p hp => pow_pos (Nat.mem_primesLE.1 hp).2.pos _)` after adjusting the coercions. Establish `hlog : Real.log ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`.

Rewrite using `[Nat.cast_pow, Real.log_pow]`. Introduce `p hp`. Establish `: (0 : ℝ) < p` using `by exact_mod_cast (Nat.mem_primesLE.1 hp).2.pos`. Rewrite using `[Nat.cast_pow]`. Conclude with `pow_ne_zero _ this.ne'`.

Rewrite using `[← hlog]`. Conclude with `Real.log_le_log hpos hle`.
-/
lemma sum_div_mul_log_le_log_factorial (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∏ p ∈ s, p ^ (n / p) ∣ n.factorial := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp
    · intro a s ha ih h
      rw [Finset.prod_insert ha]
      have hs := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
      have haP := h a (Finset.mem_insert_self a s)
      have hcop : Nat.Coprime (a ^ (n / a)) (∏ p ∈ s, p ^ (n / p)) := by
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.prod_right
        intro p hp
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes haP (h p (Finset.mem_insert_of_mem hp))).2
          (fun e => ha (by rw [e]; exact hp))
      exact hcop.mul_dvd_of_dvd_of_dvd
        ((haP.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n)).2
          (div_le_factorization_factorial haP n)) hs
  have hd : ∏ p ∈ Nat.primesLE n, p ^ (n / p) ∣ n.factorial :=
    key _ (fun p hp => (Nat.mem_primesLE.1 hp).2)
  have hle : ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) ≤ (n.factorial : ℕ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos n) hd
  have hpos : (0 : ℝ) < ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => pow_pos (Nat.mem_primesLE.1 hp).2.pos _)
  have hlog : Real.log ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p := by
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p _
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.1 hp).2.pos
      rw [Nat.cast_pow]
      exact pow_ne_zero _ this.ne'
  rw [← hlog]
  exact Real.log_le_log hpos hle

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `h1 : (0 : ℝ) < (n.factorial : ℕ)` using `by exact_mod_cast Nat.factorial_pos n`. Establish `h2 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n` using `by exact_mod_cast Nat.factorial_le_pow n`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma log_factorial_le (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
    have h2 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h1 h2
      _ = n * Real.log n := by rw [Real.log_pow]

/- English proof (translation)
Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hprim : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4`. Establish `h4 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n` using `by exact_mod_cast primorial_le_4_pow n`. Establish `hpos : (0 : ℝ) < (primorial n : ℕ)` using `by exact_mod_cast primorial_pos n`. Establish `hlog : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p`.

Unfold `primorial`. Rewrite using `[Nat.cast_prod, Real.log_prod]`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `p`. Simplify using `[Nat.mem_primesLE, Nat.lt_succ_iff, and_comm]`.

Introduce `p hp`. Use `(Finset.mem_filter.1 hp).2.pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[← hlog, ← Real.log_pow]`. Conclude with `Real.log_le_log hpos h4`.

Establish `hterm : ∀ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p`. Introduce `p hp`. Establish `hpp` using `(Nat.mem_primesLE.1 hp).2`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hpp.pos`. Establish `hlogp : 0 ≤ Real.log p` using `Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)`.

Establish `hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1`. Rewrite using `[div_le_iff₀ hp0]`. Establish `h3 : n < n / p * p + p` using `Nat.lt_div_mul_add hpp.pos`. Establish `h4 : (n : ℝ) ≤ ((n / p * p + p : ℕ) : ℝ)` using `by exact_mod_cast h3.le`. Move the coercions through the operations in `at h4`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4)`. Rewrite using `[Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.

Use `log_factorial_le n` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_left hsum hnpos`.
-/
lemma sum_primesLE_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hprim : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    have h4 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_4_pow n
    have hpos : (0 : ℝ) < (primorial n : ℕ) := by exact_mod_cast primorial_pos n
    have hlog : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p := by
      unfold primorial
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr _ (fun _ _ => rfl)
        ext p
        simp [Nat.mem_primesLE, Nat.lt_succ_iff, and_comm]
      · intro p hp
        have := (Finset.mem_filter.1 hp).2.pos
        exact_mod_cast this.ne'
    rw [← hlog, ← Real.log_pow]
    exact Real.log_le_log hpos h4
  have hterm : ∀ p ∈ Nat.primesLE n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have h3 : n < n / p * p + p := Nat.lt_div_mul_add hpp.pos
      have h4 : (n : ℝ) ≤ ((n / p * p + p : ℕ) : ℝ) := by exact_mod_cast h3.le
      push_cast at h4
      linarith
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hdiv hlogp
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
      ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ Nat.primesLE n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hterm
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
          + ∑ p ∈ Nat.primesLE n, Real.log p := Finset.sum_add_distrib
      _ ≤ Real.log (n.factorial : ℕ) + n * Real.log 4 :=
          add_le_add (sum_div_mul_log_le_log_factorial n) hprim
      _ ≤ n * (Real.log n + Real.log 4) := by
          have := log_factorial_le n
          nlinarith
  exact le_of_mul_le_mul_left hsum hnpos

end Formalism.LogFactorialBounds
