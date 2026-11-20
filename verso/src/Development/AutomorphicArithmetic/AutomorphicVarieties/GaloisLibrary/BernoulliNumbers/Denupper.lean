import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUpper

open Finset UpperTheory.V.Bern

/- English proof (translation)
Establish `hb` using `b_upper k Φ hM hΦ`. Establish `hp : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1)` using `by exact_mod_cast primorial_le_4_pow (k + 1)`. Establish `h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k` using `pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k`. Establish `hpi : 0 < (2 * Real.pi) ^ k` using `by positivity`. Establish `hMN' : (M : ℝ) ≤ N` using `by exact_mod_cast hMN`.

Rewrite using `[norm_mul, Complex.norm_natCast, den, bnd]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hb.trans (by gcongr)`. Use `_ = 16 * (N : ℝ) ^ (k + 1) * k.factorial * (4 ^ k / (2 * Real.pi) ^ k) := by ring`.

Use `_ ≤ 16 * (N : ℝ) ^ (k + 1) * k.factorial * 1 := by gcongr`. Rewrite using `[div_le_one hpi]`. Conclude with `h4`. Use `_ = _ := mul_one _`.
-/
private theorem bernoulli_denominator_bound {N M : ℕ} (k : ℕ) (Φ : ZMod M → ℂ) (hM : 0 < M) (hMN : M ≤ N)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1) : ‖(den N k : ℂ) * genB k Φ‖ ≤ bnd N k := by
  have hb := b_upper k Φ hM hΦ
  have hp : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := by exact_mod_cast primorial_le_4_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  have hpi : 0 < (2 * Real.pi) ^ k := by positivity
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  rw [norm_mul, Complex.norm_natCast, den, bnd]
  push_cast
  calc (N : ℝ) * (primorial (k + 1) : ℝ) * ‖genB k Φ‖
      ≤ N * 4 ^ (k + 1) * (4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k) := by
        gcongr
        exact hb.trans (by gcongr)
    _ = 16 * (N : ℝ) ^ (k + 1) * k.factorial * (4 ^ k / (2 * Real.pi) ^ k) := by ring
    _ ≤ 16 * (N : ℝ) ^ (k + 1) * k.factorial * 1 := by
        gcongr
        rw [div_le_one hpi]
        exact h4
    _ = _ := mul_one _

/- English proof (translation)
Introduce `N _ k χ`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Use `⟨bernoulli_denominator_bound k _ hN le_rfl (fun a => χ.norm_le_one a), ?_, ?_⟩` and prove the remaining obligations. Conclude with `bernoulli_denominator_bound k _ (Nat.pos_of_ne_zero χ.conductor_ne_zero) (Nat.le_of_dvd hN χ.conductor_dvd_level) (fun a => χ.primitiveCharacter.norm_le_one a)`. Establish `h1 : (1 : ℝ) ≤ (N : ℝ) ^ (k + 1)` using `one_le_pow₀ (by exact_mod_cast hN)`.

Establish `h2 : (1 : ℝ) ≤ (k.factorial : ℝ)` using `by exact_mod_cast k.factorial_pos`. Unfold `bnd`. Use polynomial arithmetic with `[mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)]`.
-/
theorem UpperTheory.V.Bern.b_denupper :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter ℂ N), ‖(den N k : ℂ) * genB k χ‖ ≤ bnd N k ∧ ‖(den N k : ℂ) * Bprim k χ‖ ≤ bnd N k ∧ 1 ≤ bnd N k := by
  intro N _ k χ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨bernoulli_denominator_bound k _ hN le_rfl (fun a => χ.norm_le_one a), ?_, ?_⟩
  · exact bernoulli_denominator_bound k _ (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (Nat.le_of_dvd hN χ.conductor_dvd_level) (fun a => χ.primitiveCharacter.norm_le_one a)
  · have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (k + 1) := one_le_pow₀ (by exact_mod_cast hN)
    have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    unfold bnd
    nlinarith [mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)]
