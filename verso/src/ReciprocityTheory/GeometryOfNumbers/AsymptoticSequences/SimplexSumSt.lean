import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Asymptotics Finset

namespace SimplexSum

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1 : 0 ≤ x ^ k` using `pow_nonneg hx k`. Establish `h2 : 0 ≤ (k : ℝ) + 1` using `by positivity`.

Rewrite using `[show x ^ (k + 1 + 1) = x ^ k * x * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring, show x ^ (k + 1) = x ^ k * x by ring]`. Rewrite `ih` using `[show x ^ (k + 1) = x ^ k * x by ring]`. Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1), mul_nonneg h2 h1]`.
-/
theorem pow_succ_lower (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    x ^ (k + 1) + (k + 1) * x ^ k ≤ (x + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ x ^ k := pow_nonneg hx k
    have h2 : 0 ≤ (k : ℝ) + 1 := by positivity
    rw [show x ^ (k + 1 + 1) = x ^ k * x * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring,
      show x ^ (k + 1) = x ^ k * x by ring]
    rw [show x ^ (k + 1) = x ^ k * x by ring] at ih
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1), mul_nonneg h2 h1]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h3 : x ^ (k + 1) ≤ (x + 1) ^ (k + 1)` using `pow_le_pow_left₀ hx (by linarith) _`. Rewrite using `[show x ^ (k + 1 + 1) = x ^ (k + 1) * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring]`.

Rewrite `ih`, `h3`, the goal using `[show (x + 1) ^ (k + 1) = (x + 1) ^ k * (x + 1) by ring]`. Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1)]`.
-/
theorem pow_succ_upper (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (x + 1) ^ (k + 1) ≤ x ^ (k + 1) + (k + 1) * (x + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h3 : x ^ (k + 1) ≤ (x + 1) ^ (k + 1) := pow_le_pow_left₀ hx (by linarith) _
    rw [show x ^ (k + 1 + 1) = x ^ (k + 1) * x by ring, show (x + 1) ^ (k + 1 + 1) = (x + 1) ^ (k + 1) * (x + 1) by ring]
    rw [show (x + 1) ^ (k + 1) = (x + 1) ^ k * (x + 1) by ring] at ih h3 ⊢
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ x + 1)]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [zero_add, range_one, sum_singleton, Nat.cast_zero]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[pow_succ, mul_zero]`.

Check the signs of the components of the expression. Rewrite using `[pow_succ, mul_zero, zero_add]`. Consider the case `succ n ih`. Take `⟨ih1, ih2⟩` from `ih`. Rewrite using `[sum_range_succ]`.

Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hl` using `pow_succ_lower (n : ℝ) hn k`. Establish `hu` using `pow_succ_upper (n : ℝ) hn k`. Use `push_cast`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem sum_bounds (k n : ℕ) :
    (n : ℝ) ^ (k + 1) ≤ (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ∧
      (k + 1) * ∑ a ∈ range (n + 1), (a : ℝ) ^ k ≤ (n : ℝ) ^ (k + 1) + (k + 1) * (n : ℝ) ^ k := by
  induction n with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero]
    constructor
    · rw [pow_succ, mul_zero]; positivity
    · rw [pow_succ, mul_zero, zero_add]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hl := pow_succ_lower (n : ℝ) hn k
    have hu := pow_succ_upper (n : ℝ) hn k
    push_cast
    constructor <;> nlinarith

def S (i j n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, (p.1 : ℝ) ^ i * (p.2 : ℝ) ^ j

/- English proof (translation)
Unfold `S`. Rewrite using `[Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using the standard rewrite rules.
-/
theorem S_zero (i n : ℕ) : S i 0 n = ∑ a ∈ range (n + 1), (a : ℝ) ^ i := by
  unfold S
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/- English proof (translation)
Unfold `S`. Rewrite using `[mul_sum, ← sum_sub_distrib]`. Apply `sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `: (p.2 : ℝ) = n - p.1` using `by rw [← hp]; push_cast; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem S_succ (i j n : ℕ) : S i (j + 1) n = n * S i j n - S (i + 1) j n := by
  unfold S
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : (p.2 : ℝ) = n - p.1 := by rw [← hp]; push_cast; ring
  rw [this]; ring

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `i`. Use `IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Take `⟨hb1, hb2⟩` from `sum_bounds i n`.

Simplify using `only [S_zero, Nat.factorial_zero, Nat.cast_one, mul_one, add_zero]`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ i), one_mul, Nat.factorial_succ]`. Use `push_cast`. Establish `hf : (1 : ℝ) ≤ i.factorial` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)`. Establish `hi : (0 : ℝ) ≤ (i : ℝ) + 1` using `by positivity`.

Establish `hp : (0 : ℝ) ≤ (n : ℝ) ^ i` using `by positivity`. Use `set T := ∑ a ∈ range (n + 1), (a : ℝ) ^ i`. Establish `key : T / i.factorial - (n : ℝ) ^ (i + 1) / (((i : ℝ) + 1) * i.factorial) = (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key, abs_le]`.

Prove the components needed by the constructor for the conclusion. Establish `: 0 ≤ (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial)` using `div_nonneg (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hp hi) (by linarith : (0:ℝ) ≤ i.factorial - 1)]`.

Consider the case `succ j ih`. Introduce `i`. Establish `h1` using `((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul (ih i)).const_mul_left (1 / ((j : ℝ) + 1))`. Establish `h2` using `(ih (i + 1)).const_mul_left (((i : ℝ) + 1) / ((j : ℝ) + 1))`. Establish `h2' : (fun x : ℕ => ((i : ℝ) + 1) / ((j : ℝ) + 1) * (S (i + 1) j x / (((i + 1).factorial : ℝ) * (j.factorial : ℝ)) - (x : ℝ) ^ (i + 1 + j + 1) / ((i + 1 + j + 1).factorial : ℝ))) =O[atTop] fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (i + j)` using `h2.congr_right (fun n => by ring)`.

Use `(h1.sub h2').congr' ?_ ?_` and prove the remaining obligations. Use `Eventually.of_forall fun n => ?_ dsimp only` and prove the remaining obligations. Rewrite using `[S_succ]`. Rewrite using `[show i + (j + 1) + 1 = i + j + 1 + 1 by ring, show i + 1 + j + 1 = i + j + 1 + 1 by ring, Nat.factorial_succ (i + j + 1), Nat.factorial_succ j, Nat.factorial_succ i]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `Eventually.of_forall fun n => ?_ dsimp only` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main (j : ℕ) : ∀ i : ℕ, (fun n : ℕ => S i j n / ((i.factorial : ℝ) * (j.factorial : ℝ)) -
      (n : ℝ) ^ (i + j + 1) / ((i + j + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (i + j) := by
  induction j with
  | zero =>
    intro i
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    obtain ⟨hb1, hb2⟩ := sum_bounds i n
    simp only [S_zero, Nat.factorial_zero, Nat.cast_one, mul_one, add_zero]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ i), one_mul,
      Nat.factorial_succ]
    push_cast
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hi : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) ≤ (n : ℝ) ^ i := by positivity
    set T := ∑ a ∈ range (n + 1), (a : ℝ) ^ i
    have key : T / i.factorial - (n : ℝ) ^ (i + 1) / (((i : ℝ) + 1) * i.factorial) =
        (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) := by
      field_simp
    rw [key, abs_le]
    constructor
    · have : 0 ≤ (((i : ℝ) + 1) * T - (n : ℝ) ^ (i + 1)) / (((i : ℝ) + 1) * i.factorial) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hp hi) (by linarith : (0:ℝ) ≤ i.factorial - 1)]
  | succ j ih =>
    intro i
    have h1 := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul (ih i)).const_mul_left (1 / ((j : ℝ) + 1))
    have h2 := (ih (i + 1)).const_mul_left (((i : ℝ) + 1) / ((j : ℝ) + 1))
    have h2' : (fun x : ℕ => ((i : ℝ) + 1) / ((j : ℝ) + 1) *
        (S (i + 1) j x / (((i + 1).factorial : ℝ) * (j.factorial : ℝ)) -
          (x : ℝ) ^ (i + 1 + j + 1) / ((i + 1 + j + 1).factorial : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (i + j) := h2.congr_right (fun n => by ring)
    refine (h1.sub h2').congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      rw [S_succ]
      rw [show i + (j + 1) + 1 = i + j + 1 + 1 by ring, show i + 1 + j + 1 = i + j + 1 + 1 by ring,
        Nat.factorial_succ (i + j + 1), Nat.factorial_succ j, Nat.factorial_succ i]
      push_cast
      field_simp
      ring
    · refine Eventually.of_forall fun n => ?_
      dsimp only
      ring

end SimplexSum

end ReciprocityTheory.GeometryOfNumbersTheory
