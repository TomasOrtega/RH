import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
/- English proof (translation)
Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases. Simplify using `using Real.log_nonneg hC`. Establish `h1 : Nat.log l m ≤ Nat.log 2 m` using `Nat.log_anti_left (by norm_num) hl`. Establish `h2 : 2 ^ Nat.log 2 m ≤ m` using `Nat.pow_log_le_self 2 hpos.ne'`. Establish `h3 : (2 : ℝ) ^ Nat.log l m ≤ C`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `Real.log_le_log (by positivity) h3`. Rewrite `h4` using `[Real.log_pow]`. Then use the resulting hypothesis.
-/
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
/- English proof (translation)
Establish `hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)`. Establish `h` using `natLog_mul_log_two_le_log_of_le hl hC hm`. Rewrite `h` using `[Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]`. Establish `hlog : (1 : ℝ) / 2 < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `: ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith

open NumberField IsDedekindDomain Module in

/- English proof (translation)
Introduce `l N L hl hN hL`. Establish `hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L` using `Nat.floor_le (by positivity)`. Establish `he : 1 ≤ Real.exp L` using `Real.one_le_exp (by linarith)`. Establish `hm : ((2 * (⌊2 * Real.exp L⌋₊ + 1) : ℕ) : ℝ) ≤ 2 ^ 3 * Real.exp L`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hK` using `natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm`. Move the coercions through the operations in `at hK ⊢`. Use `set K : ℝ := (Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) : ℝ)`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hK0 : 0 ≤ K` using `Nat.cast_nonneg _`. Establish `hNL : (1 : ℝ) ≤ N * L` using `one_le_mul_of_one_le_of_one_le hN' hL`. Establish `hL1 : L ≤ N * L` using `by nlinarith`. Establish `hN1 : (N : ℝ) ≤ N * L` using `by nlinarith`. Establish `hA : (N : ℝ) * K ≤ N * (3 + 2 * L)`.

Apply `mul_le_mul_of_nonneg_left hK` to reduce the goal to its premises. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem _root_.GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul :
    ∀ (l N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ N → 1 ≤ L →
      ((5 + Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) +
        N * (4 + 2 * Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1))) : ℕ) : ℝ) ≤ 25 * N * L := by
  intro l N L hl hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have he : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hm : ((2 * (⌊2 * Real.exp L⌋₊ + 1) : ℕ) : ℝ) ≤ 2 ^ 3 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * (⌊2 * Real.exp L⌋₊ + 1)) : ℝ)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hNL : (1 : ℝ) ≤ N * L := one_le_mul_of_one_le_of_one_le hN' hL
  have hL1 : L ≤ N * L := by nlinarith
  have hN1 : (N : ℝ) ≤ N * L := by nlinarith
  have hA : (N : ℝ) * K ≤ N * (3 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
