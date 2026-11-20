import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalFibPowExplicit
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.LineForm

namespace GlobalTheory.LineForm.PolyId

def tm (n j : ℕ) : MvPolynomial (Fin 2) ℝ := C ((-1) ^ j * ((n - j).choose j : ℝ)) * X 0 ^ (n - 2 * j) * X 1 ^ j

/- English proof (translation)
Simplify using `[tm, Nat.choose_eq_zero_of_lt (show n - j < j by omega)]`.
-/
theorem tm_eq_zero (n j : ℕ) (h : n < j) : tm n j = 0 := by
  simp [tm, Nat.choose_eq_zero_of_lt (show n - j < j by omega)]

/- English proof (translation)
Unfold `hs`. Conclude with `Finset.sum_subset (Finset.range_mono hK) (fun j hj hj' => by`. Simplify using `only [Finset.mem_range] at hj hj'; exact tm_eq_zero n j (by omega))`.
-/
theorem hs_eq (n K : ℕ) (hK : n + 1 ≤ K) : hs n = ∑ j ∈ Finset.range K, tm n j := by
  unfold hs
  exact Finset.sum_subset (Finset.range_mono hK) (fun j hj hj' => by
    simp only [Finset.mem_range] at hj hj'; exact tm_eq_zero n j (by omega))

/- English proof (translation)
Break down `le_or_gt j n with h | h` into its components or cases. Rewrite using `[show n + 2 - (j + 1) = (n - j) + 1 by omega, show n + 1 - (j + 1) = n - j by omega, Nat.choose_succ_succ']`. Rewrite using `[show n + 2 - (j + 1) = 0 by omega, show n - j = 0 by omega, show n + 1 - (j + 1) = 0 by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]`.
-/
theorem pascal (n j : ℕ) : (n + 2 - (j + 1)).choose (j + 1) = (n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) := by
  rcases le_or_gt j n with h | h
  · rw [show n + 2 - (j + 1) = (n - j) + 1 by omega, show n + 1 - (j + 1) = n - j by omega, Nat.choose_succ_succ']
  · rw [show n + 2 - (j + 1) = 0 by omega, show n - j = 0 by omega, show n + 1 - (j + 1) = 0 by omega,
      Nat.choose_eq_zero_of_lt (by omega : 0 < j + 1), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]

/- English proof (translation)
Establish `hb : C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ (n - 2 * j) = X 0 * (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (n + 1 - 2 * (j + 1)))`. Distinguish the cases in `h : 2 * j + 1 ≤ n`. Rewrite using `[show n - 2 * j = (n + 1 - 2 * (j + 1)) + 1 by omega, pow_succ]; ring`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega : n + 1 - (j + 1) < j + 1)]; simp`. Establish `hC : C ((-1) ^ (j + 1) * ((((n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) : ℕ)) : ℝ)) = (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) - C ((-1) ^ j * ((n - j).choose j : ℝ)) : MvPolynomial (Fin 2) ℝ)`.

Rewrite using `[← C_sub]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [tm]`.

Rewrite using `[pascal, show n + 2 - 2 * (j + 1) = n - 2 * j by omega, hC]`. Take the linear combination `X 1 ^ (j + 1) * hb`.
-/
theorem tm_rec (n j : ℕ) : tm (n + 2) (j + 1) = X 0 * tm (n + 1) (j + 1) - X 1 * tm n j := by
  have hb : C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ (n - 2 * j) =
      X 0 * (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (n + 1 - 2 * (j + 1))) := by
    by_cases h : 2 * j + 1 ≤ n
    · rw [show n - 2 * j = (n + 1 - 2 * (j + 1)) + 1 by omega, pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 - (j + 1) < j + 1)]; simp
  have hC : C ((-1) ^ (j + 1) * ((((n - j).choose j + (n + 1 - (j + 1)).choose (j + 1) : ℕ)) : ℝ)) =
      (C ((-1) ^ (j + 1) * ((n + 1 - (j + 1)).choose (j + 1) : ℝ)) - C ((-1) ^ j * ((n - j).choose j : ℝ)) :
        MvPolynomial (Fin 2) ℝ) := by
    rw [← C_sub]; congr 1; push_cast; ring
  simp only [tm]
  rw [pascal, show n + 2 - 2 * (j + 1) = n - 2 * j by omega, hC]
  linear_combination X 1 ^ (j + 1) * hb

/- English proof (translation)
Rewrite using `[hs_eq (n + 2) (n + 2 + 1) le_rfl, hs_eq (n + 1) (n + 2 + 1) (by omega), hs_eq n (n + 2) (by omega), Finset.sum_range_succ', Finset.sum_range_succ' (fun j => tm (n + 1) j)]`. Repeatedly rewrite using `[tm_rec]`. Rewrite using `[Finset.sum_sub_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]`. Establish `h0 : tm (n + 2) 0 = X 0 * tm (n + 1) 0` using `by simp [tm]; ring`. Rewrite using `[h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hs_rec (n : ℕ) : hs (n + 2) = X 0 * hs (n + 1) - X 1 * hs n := by
  rw [hs_eq (n + 2) (n + 2 + 1) le_rfl, hs_eq (n + 1) (n + 2 + 1) (by omega), hs_eq n (n + 2) (by omega),
    Finset.sum_range_succ', Finset.sum_range_succ' (fun j => tm (n + 1) j)]
  simp_rw [tm_rec]
  rw [Finset.sum_sub_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h0 : tm (n + 2) 0 = X 0 * tm (n + 1) 0 := by simp [tm]; ring
  rw [h0]; ring

/- English proof (translation)
Establish `key : ∀ n : ℕ, (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) ∧ (a - b) * eval ![a + b, a * b] (hs (n + 1)) = a ^ (n + 2) - b ^ (n + 2)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => constructor <;> simp [hs, Finset.sum_range_succ] <;> ring`. Consider the case `succ n ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hs_rec]`. Simplify using `only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Take the linear combination `(a + b) * ih.2 - a * b * ih.1`. Conclude with `(key n).1`.
-/
theorem eval_hs_mul (a b : ℝ) (n : ℕ) :
    (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) := by
  have key : ∀ n : ℕ, (a - b) * eval ![a + b, a * b] (hs n) = a ^ (n + 1) - b ^ (n + 1) ∧
      (a - b) * eval ![a + b, a * b] (hs (n + 1)) = a ^ (n + 2) - b ^ (n + 2) := by
    intro n
    induction n with
    | zero => constructor <;> simp [hs, Finset.sum_range_succ] <;> ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hs_rec]
      simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linear_combination (a + b) * ih.2 - a * b * ih.1
  exact (key n).1

/- English proof (translation)
Establish `hd : a - b ≠ 0` using `sub_ne_zero.mpr hab`. Establish `e : (fun t : ℝ => (t * a + (1 - t) * b) ^ n) = fun t => (fun x : ℝ => x ^ n) ((a - b) * t + b)`. Use function extensionality and compare the values at `t`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ n) hd, integral_pow]`.

Simplify using `only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]`. Establish `hn : (n : ℝ) + 1 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_affine (a b : ℝ) (hab : a ≠ b) (n : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n = (a ^ (n + 1) - b ^ (n + 1)) / (((n : ℝ) + 1) * (a - b)) := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have e : (fun t : ℝ => (t * a + (1 - t) * b) ^ n) = fun t => (fun x : ℝ => x ^ n) ((a - b) * t + b) := by
    funext t; ring
  rw [e, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x ^ n) hd, integral_pow]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Establish `h : ((j : ℝ) + j + 1) * ((j + j).choose j : ℝ) * ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j = 1` using `ReciprocityTheory.GeometryOfNumbersTheory.bI_closed j j`. Establish `hc` using `Nat.choose_mul_factorial_mul_factorial (show j ≤ j + j by omega)`. Rewrite `hc` using `[show j + j - j = j by omega]`. Establish `hc' : ((j + j).choose j : ℝ) * j.factorial * j.factorial = (j + j).factorial` using `by exact_mod_cast hc`. Establish `hf : ((2 * j + 1).factorial : ℝ) = (2 * (j : ℝ) + 1) * (j + j).factorial`.

Rewrite using `[show 2 * j + 1 = (j + j) + 1 by omega, Nat.factorial_succ]; push_cast; ring`. Establish `hpos : ((2 * j + 1).factorial : ℝ) ≠ 0` using `by positivity`. Rewrite using `[eq_div_iff hpos, hf]`. Express the relevant statement in the definitionally equal form `ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j * _ = _`. Take the linear combination `(-(ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j) * (2 * (j : ℝ) + 1)) * hc' + ((j.factorial : ℝ) * j.factorial) * h`.
-/
theorem beta_eq (j : ℕ) :
    ∫ t in (0:ℝ)..1, t ^ j * (1 - t) ^ j = (j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial := by
  have h : ((j : ℝ) + j + 1) * ((j + j).choose j : ℝ) * ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j = 1 := ReciprocityTheory.GeometryOfNumbersTheory.bI_closed j j
  have hc := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + j by omega)
  rw [show j + j - j = j by omega] at hc
  have hc' : ((j + j).choose j : ℝ) * j.factorial * j.factorial = (j + j).factorial := by exact_mod_cast hc
  have hf : ((2 * j + 1).factorial : ℝ) = (2 * (j : ℝ) + 1) * (j + j).factorial := by
    rw [show 2 * j + 1 = (j + j) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have hpos : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hpos, hf]
  change ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j * _ = _
  linear_combination (-(ReciprocityTheory.GeometryOfNumbersTheory.betaNatInt j j) * (2 * (j : ℝ) + 1)) * hc' + ((j.factorial : ℝ) * j.factorial) * h

/- English proof (translation)
Establish `hE : ∀ n : ℕ, eval ![a + b, a * b] (hs n) = ((n : ℝ) + 1) * ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n`. Introduce `n`. Rewrite using `[integral_affine a b hab n]`. Establish `h` using `eval_hs_mul a b n`. Establish `hd : a - b ≠ 0` using `sub_ne_zero.mpr hab`.

Establish `hn : (n : ℝ) + 1 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Establish `hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m = ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (m.choose j : ℝ) * (a + b) ^ (m - j) * (t * a + (1 - t) * b) ^ (m + j)`. Introduce `t`.

Rewrite using `[show a + b - (t * a + (1 - t) * b) = -(t * a + (1 - t) * b) + (a + b) by ring, add_pow (-(t * a + (1 - t) * b)) (a + b) m, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[neg_pow]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hI]`.

Rewrite using `[intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]`. Simplify using `only [map_sum, map_mul, eval_C, map_pow, eval_X, hE]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[intervalIntegral.integral_const_mul]`. Simplify using `only [Matrix.cons_val_zero]`.

Establish `hp : (m : ℝ) + j + 1 ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.
-/
theorem eval_lhs (a b : ℝ) (hab : a ≠ b) (m : ℕ) :
    eval ![a + b, a * b] (∑ j ∈ Finset.range (m + 1),
      C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j))
      = ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m := by
  have hE : ∀ n : ℕ, eval ![a + b, a * b] (hs n) = ((n : ℝ) + 1) * ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ n := by
    intro n
    rw [integral_affine a b hab n]
    have h := eval_hs_mul a b n
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    linear_combination h
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (m.choose j : ℝ) * (a + b) ^ (m - j) * (t * a + (1 - t) * b) ^ (m + j) := by
    intro t
    rw [show a + b - (t * a + (1 - t) * b) = -(t * a + (1 - t) * b) + (a + b) by ring, add_pow (-(t * a + (1 - t) * b)) (a + b) m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow]; ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [map_sum, map_mul, eval_C, map_pow, eval_X, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp only [Matrix.cons_val_zero]
  have hp : (m : ℝ) + j + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

/- English proof (translation)
Establish `hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m = ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (a * b) ^ (m - j) * ((a + b) ^ 2 - 4 * (a * b)) ^ j) * (t ^ j * (1 - t) ^ j)`. Introduce `t`. Rewrite using `[← mul_pow, show (t * a + (1 - t) * b) * (a + b - (t * a + (1 - t) * b)) = t * (1 - t) * ((a + b) ^ 2 - 4 * (a * b)) + a * b by ring, add_pow]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hI]`. Rewrite using `[intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]`. Simplify using `only [pm, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[intervalIntegral.integral_const_mul, beta_eq]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_rhs (a b : ℝ) (m : ℕ) :
    ∫ t in (0:ℝ)..1, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m = eval ![a + b, a * b] (pm m) := by
  have hI : ∀ t : ℝ, (t * a + (1 - t) * b) ^ m * (a + b - (t * a + (1 - t) * b)) ^ m =
      ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (a * b) ^ (m - j) * ((a + b) ^ 2 - 4 * (a * b)) ^ j) *
        (t ^ j * (1 - t) ^ j) := by
    intro t
    rw [← mul_pow, show (t * a + (1 - t) * b) * (a + b - (t * a + (1 - t) * b)) =
      t * (1 - t) * ((a + b) ^ 2 - 4 * (a * b)) + a * b by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, mul_pow]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, beta_eq]
  simp
  ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C r => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp, aeval_X, map_X, eval_X]`.

Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem eval_map_aeval (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℂ) :
    eval z ((aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ).map (algebraMap ℝ ℂ)) =
      eval ![z 0 + z 1, z 0 * z 1] (P.map (algebraMap ℝ ℂ)) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, map_X, eval_X]
    fin_cases i <;> simp

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C r => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp, aeval_X, eval_X]`.

Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem eval_aeval_sym (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    eval x (aeval ![X 0 + X 1, X 0 * X 1] P : MvPolynomial (Fin 2) ℝ) = eval ![x 0 + x 1, x 0 * x 1] P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    fin_cases i <;> simp

/- English proof (translation)
Use `set Q : MvPolynomial (Fin 2) ℝ := aeval ![X 0 + X 1, X 0 * X 1] P with hQ`. Establish `hQe : ∀ x : Fin 2 → ℝ, eval x Q = eval ![x 0 + x 1, x 0 * x 1] P`. Introduce `x`. Rewrite using `[hQ, eval_aeval_sym]`. Establish `hXQ : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) * Q = 0`.

Use `MvPolynomial.funext fun x => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_zero, hQe]`. Distinguish the cases in `hx : x 0 = x 1`. Simplify using `[hx]`. Simplify using `[h _ _ hx]`.

Establish `hX : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0`. Introduce `h0`. Use `congrArg (eval ![1, 0]) h0` as an intermediate fact. Simplify using `at this`. Establish `hQ0 : Q = 0` using `(mul_eq_zero.mp hXQ).resolve_left hX`.

Establish `hPm : P.map (algebraMap ℝ ℂ) = 0`. Use `GlobalTheory.FibLine.eq_zero_of_eval_symm _ fun a b => ?_` and prove the remaining obligations. Use `eval_map_aeval P ![a, b]` as an intermediate fact. Rewrite `this` using `[← hQ, hQ0]`. Simplify using `using this.symm`.

Conclude with `MvPolynomial.map_injective _ (algebraMap ℝ ℂ).injective (by simpa using hPm)`.
-/
theorem eq_zero_of_symm_real (P : MvPolynomial (Fin 2) ℝ) (h : ∀ a b : ℝ, a ≠ b → eval ![a + b, a * b] P = 0) :
    P = 0 := by
  set Q : MvPolynomial (Fin 2) ℝ := aeval ![X 0 + X 1, X 0 * X 1] P with hQ
  have hQe : ∀ x : Fin 2 → ℝ, eval x Q = eval ![x 0 + x 1, x 0 * x 1] P := by
    intro x
    rw [hQ, eval_aeval_sym]
  have hXQ : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) * Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, hQe]
    by_cases hx : x 0 = x 1
    · simp [hx]
    · simp [h _ _ hx]
  have hX : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h0
    have := congrArg (eval ![1, 0]) h0
    simp at this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hXQ).resolve_left hX
  have hPm : P.map (algebraMap ℝ ℂ) = 0 := by
    refine GlobalTheory.FibLine.eq_zero_of_eval_symm _ fun a b => ?_
    have := eval_map_aeval P ![a, b]
    rw [← hQ, hQ0] at this
    simpa using this.symm
  exact MvPolynomial.map_injective _ (algebraMap ℝ ℂ).injective (by simpa using hPm)

end GlobalTheory.LineForm.PolyId

namespace GlobalTheory.LineForm

open PolyId in

/- English proof (translation)
Introduce `m`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_symm_real _ fun a b hab => ?_` and prove the remaining obligations. Rewrite using `[map_sub, eval_lhs a b hab m, eval_rhs a b m, sub_self]`.
-/
theorem sum_choose_hs_eq_pm : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1),
    C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  intro m
  rw [← sub_eq_zero]
  refine eq_zero_of_symm_real _ fun a b hab => ?_
  rw [map_sub, eval_lhs a b hab m, eval_rhs a b m, sub_self]

end GlobalTheory.LineForm
