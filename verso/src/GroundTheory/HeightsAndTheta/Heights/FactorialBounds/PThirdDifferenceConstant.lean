import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Establish `hv' : 0 < |v|` using `abs_pos.mpr hv`. Take `⟨n, hn⟩` from `exists_nat_gt ((K + |u|) / |v|)`. Establish `h1 : |(n : ℝ) * v| ≤ K + |u|`. Establish `: (n : ℝ) * v = (u + n * v) - u` using `by ring`.

Rewrite using `[this]`. Combine the linear relations using `[abs_sub (u + n * v) u, h n]`. Rewrite `h1` using `[abs_mul, Nat.abs_cast]`. Rewrite `hn` using `[div_lt_iff₀ hv']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ThirdDifferenceConstant.step_zero_of_bounded (u v K : ℝ)
    (h : ∀ n : ℕ, |u + n * v| ≤ K) : v = 0 := by
  by_contra hv
  have hv' : 0 < |v| := abs_pos.mpr hv
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + |u|) / |v|)
  have h1 : |(n : ℝ) * v| ≤ K + |u| := by
    have : (n : ℝ) * v = (u + n * v) - u := by ring
    rw [this]
    linarith [abs_sub (u + n * v) u, h n]
  rw [abs_mul, Nat.abs_cast] at h1
  rw [div_lt_iff₀ hv'] at hn
  linarith

/- English proof (translation)
Introduce `A _ f ⟨C, hC⟩ hf`. Establish `key : ∀ z : A, f z = f 0`. Introduce `z`. Establish `hrec : ∀ n : ℕ, f ((n + 1 + 1) • z) - f ((n + 1) • z) = (f ((n + 1) • z) - f (n • z)) + (f (z + z) - 2 * f z + f 0)`. Introduce `n`.

Establish `h` using `hf (n • z) z z`. Establish `e1 : (n + 1) • z = n • z + z` using `succ_nsmul z n`. Establish `e2 : (n + 1 + 1) • z = n • z + z + z` using `by rw [succ_nsmul, succ_nsmul]`. Rewrite using `[e2, e1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hd : ∀ n : ℕ, f ((n + 1) • z) - f (n • z) = (f z - f 0) + n * (f (z + z) - 2 * f z + f 0)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [hrec k, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc0 : f (z + z) - 2 * f z + f 0 = 0`. Use `ThirdDifferenceConstant.step_zero_of_bounded (f z - f 0) _ (C + C) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[← hd n]`.

Combine the linear relations using `[abs_sub (f ((n + 1) • z)) (f (n • z)), hC ((n + 1) • z), hC (n • z)]`. Establish `ha : ∀ n : ℕ, f (n • z) = f 0 + n * (f z - f 0)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Use `hd k` as an intermediate fact. Rewrite `this` using `[hc0, mul_zero, add_zero]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h0 : f z - f 0 = 0` using `ThirdDifferenceConstant.step_zero_of_bounded (f 0) _ C (fun n => by rw [← ha n]; exact hC _)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x y`. Rewrite using `[key x, key y]`.
-/
theorem ThirdDifferenceConstant.proof : ThirdDifferenceConstant.Statement := by
  intro A _ f ⟨C, hC⟩ hf
  have key : ∀ z : A, f z = f 0 := by
    intro z
    have hrec : ∀ n : ℕ, f ((n + 1 + 1) • z) - f ((n + 1) • z) =
        (f ((n + 1) • z) - f (n • z)) + (f (z + z) - 2 * f z + f 0) := by
      intro n
      have h := hf (n • z) z z
      have e1 : (n + 1) • z = n • z + z := succ_nsmul z n
      have e2 : (n + 1 + 1) • z = n • z + z + z := by rw [succ_nsmul, succ_nsmul]
      rw [e2, e1]
      linarith
    have hd : ∀ n : ℕ, f ((n + 1) • z) - f (n • z) =
        (f z - f 0) + n * (f (z + z) - 2 * f z + f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [hrec k, ih]; push_cast; ring
    have hc0 : f (z + z) - 2 * f z + f 0 = 0 := by
      refine ThirdDifferenceConstant.step_zero_of_bounded (f z - f 0) _ (C + C) (fun n => ?_)
      rw [← hd n]
      linarith [abs_sub (f ((n + 1) • z)) (f (n • z)), hC ((n + 1) • z), hC (n • z)]
    have ha : ∀ n : ℕ, f (n • z) = f 0 + n * (f z - f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have := hd k
        rw [hc0, mul_zero, add_zero] at this
        push_cast
        linarith
    have h0 : f z - f 0 = 0 :=
      ThirdDifferenceConstant.step_zero_of_bounded (f 0) _ C (fun n => by rw [← ha n]; exact hC _)
    linarith
  intro x y
  rw [key x, key y]

end GroundTheory.Heights₂.Heights
