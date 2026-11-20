import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree

namespace GlobalTheory.EX

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Break down `(not_lt.mp hc).lt_or_eq with hlt | heq` into its components or cases. Rewrite `h` using `[Nat.mod_eq_of_lt hlt]`. Conclude with `hp.one_lt.ne' h`. Substitute `heq` using the available equality.

Simplify using `at h`.
-/
theorem lt_of_prime_mod_eq_one {p M : ℕ} (hp : p.Prime) (h : p % M = 1) (hM : 0 < M) : M < p := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact hp.one_lt.ne' h
  · subst heq
    simp at h

/- English proof (translation)
Rewrite using `[← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]`.
-/
theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

/- English proof (translation)
Introduce and unpack `⟨A, hA, hS⟩`. Establish `hA0 : 0 ≤ A` using `by linarith`. Use `⟨(2 + 2 * A + (2 + 2 * A) * A) * A, by nlinarith [mul_nonneg hA0 hA0, mul_nonneg hA0 (mul_nonneg hA0 hA0)], ?_⟩` and prove the remaining obligations. Introduce `N hN`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast (by omega : 1 ≤ N)`.

Establish `hN0 : (0 : ℝ) < N` using `by linarith`. Establish `key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ (e * A)`. Introduce `M e hM hMe`. Take `⟨p, hp, hpm, hple⟩` from `hS M hM`. Use `⟨p, hp, hpm, hple.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[Real.rpow_mul hN0.le]`. Conclude with `Real.rpow_le_rpow (Nat.cast_nonneg _) hMe hA0`. Establish `h15 : ((15 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ)`. Establish `: (30 : ℝ) ≤ N` using `by exact_mod_cast hN`. Rewrite using `[Real.rpow_two]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hM1 : 2 ≤ 15 * N` using `by omega`. Take `⟨p, hp, hpm, hple⟩` from `key (15 * N) 2 hM1 h15`. Establish `hM2 : 2 ≤ 15 * N * p` using `hM1.trans (Nat.le_mul_of_pos_right _ hp.pos)`.

Establish `hb2 : ((15 * N * p : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A)`. Rewrite using `[Real.rpow_add hN0, Nat.cast_mul (15 * N) p]`. Conclude with `mul_le_mul h15 hple (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)`. Take `⟨p', hp', hpm', hple'⟩` from `key (15 * N * p) _ hM2 hb2`. Establish `hM3 : 2 ≤ 15 * N * p * p'` using `hM2.trans (Nat.le_mul_of_pos_right _ hp'.pos)`.

Establish `hb3 : ((15 * N * p * p' : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A + (2 + 2 * A) * A)`. Rewrite using `[Real.rpow_add hN0, Nat.cast_mul (15 * N * p) p']`. Conclude with `mul_le_mul hb2 hple' (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)`. Take `⟨q, hq, hqm, hqle⟩` from `key (15 * N * p * p') _ hM3 hb3`. Establish `l1 : 15 * N * p < p'` using `lt_of_prime_mod_eq_one hp' hpm' (by omega)`.

Establish `l2 : 15 * N * p * p' < q` using `lt_of_prime_mod_eq_one hq hqm (by omega)`. Establish `l3 : p ≤ 15 * N * p` using `Nat.le_mul_of_pos_left _ (by omega)`. Establish `l4 : p' ≤ 15 * N * p * p'` using `Nat.le_mul_of_pos_left _ (by omega)`. Establish `hAA` using `mul_nonneg hA0 hA0`. Establish `hAAA` using `mul_nonneg hA0 hAA`.

Use `⟨p, p', q, hp, hp', hq, by omega, by omega, by omega, hpm, mod_eq_one_of_mod_mul hpm' (by omega), ?_, ?_, ?_, hqle⟩` and prove the remaining obligations. Establish `: 15 * N * p * p' = N * (15 * p * p')` using `by ring`. Rewrite `hqm` using `[this]`. Conclude with `mod_eq_one_of_mod_mul hqm (by omega)`. Conclude with `hple.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))`.

Conclude with `hple'.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))`.
-/
theorem auxiliary_primes : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  rintro ⟨A, hA, hS⟩
  have hA0 : 0 ≤ A := by linarith
  refine ⟨(2 + 2 * A + (2 + 2 * A) * A) * A, by nlinarith [mul_nonneg hA0 hA0, mul_nonneg hA0 (mul_nonneg hA0 hA0)], ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hMe
    obtain ⟨p, hp, hpm, hple⟩ := hS M hM
    refine ⟨p, hp, hpm, hple.trans ?_⟩
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMe hA0
  have h15 : ((15 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have : (30 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.rpow_two]; push_cast; nlinarith
  have hM1 : 2 ≤ 15 * N := by omega
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 hM1 h15
  have hM2 : 2 ≤ 15 * N * p := hM1.trans (Nat.le_mul_of_pos_right _ hp.pos)
  have hb2 : ((15 * N * p : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N) p]
    exact mul_le_mul h15 hple (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨p', hp', hpm', hple'⟩ := key (15 * N * p) _ hM2 hb2
  have hM3 : 2 ≤ 15 * N * p * p' := hM2.trans (Nat.le_mul_of_pos_right _ hp'.pos)
  have hb3 : ((15 * N * p * p' : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A + (2 + 2 * A) * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N * p) p']
    exact mul_le_mul hb2 hple' (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨q, hq, hqm, hqle⟩ := key (15 * N * p * p') _ hM3 hb3
  have l1 : 15 * N * p < p' := lt_of_prime_mod_eq_one hp' hpm' (by omega)
  have l2 : 15 * N * p * p' < q := lt_of_prime_mod_eq_one hq hqm (by omega)
  have l3 : p ≤ 15 * N * p := Nat.le_mul_of_pos_left _ (by omega)
  have l4 : p' ≤ 15 * N * p * p' := Nat.le_mul_of_pos_left _ (by omega)
  have hAA := mul_nonneg hA0 hA0
  have hAAA := mul_nonneg hA0 hAA
  refine ⟨p, p', q, hp, hp', hq, by omega, by omega, by omega, hpm,
    mod_eq_one_of_mod_mul hpm' (by omega), ?_, ?_, ?_, hqle⟩
  · have : 15 * N * p * p' = N * (15 * p * p') := by ring
    rw [this] at hqm
    exact mod_eq_one_of_mod_mul hqm (by omega)
  · exact hple.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))
  · exact hple'.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))

end GlobalTheory.EX
