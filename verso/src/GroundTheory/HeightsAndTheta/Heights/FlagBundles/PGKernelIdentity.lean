import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

def kernelSum {S : Type*} [CommRing S] (a b : S) (k : ℕ) : S :=
  ∑ j ∈ range k, (a ^ (2 * j + 1) * b ^ (2 * k - 1 - 2 * j) - a ^ (2 * j) * b ^ (2 * k - 2 * j))

section kernelSum

variable {S : Type*} [CommRing S]

/- English proof (translation)
Simplify using `[kernelSum]`.
-/
theorem kernelSum_zero (a b : S) : kernelSum a b 0 = 0 := by
  simp [kernelSum]

/- English proof (translation)
Unfold `kernelSum`. Rewrite using `[sum_range_succ, mul_sum]`. Use `congr 1`. Use `sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj : j < k` using `mem_range.mp hj`.

Rewrite using `[show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega, show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]`.
-/
theorem kernelSum_succ (a b : S) (k : ℕ) :
    kernelSum a b (k + 1) =
      b ^ 2 * kernelSum a b k + (a ^ (2 * k + 1) * b - a ^ (2 * k) * b ^ 2) := by
  unfold kernelSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj : j < k := mem_range.mp hj
    rw [show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega,
      show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]
    ring
  · rw [show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [kernelSum_zero]`. Consider the case `succ k ih`. Rewrite using `[kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]`. Take the linear combination `b ^ 2 * ih`.
-/
theorem add_mul_kernelSum (a b : S) (k : ℕ) :
    (a + b) * kernelSum a b k = b * (a ^ (2 * k) - b ^ (2 * k)) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    linear_combination b ^ 2 * ih

/- English proof (translation)
Simplify using `[kernelSum, map_sum, map_sub, map_mul, map_pow]`.
-/
theorem map_kernelSum {T : Type*} [CommRing T] (φ : S →+* T) (a b : S) (k : ℕ) :
    φ (kernelSum a b k) = kernelSum (φ a) (φ b) k := by
  simp [kernelSum, map_sum, map_sub, map_mul, map_pow]

/- English proof (translation)
Simplify using `[kernelSum]`.
-/
theorem kernelSum_one_one (k : ℕ) : kernelSum (1 : S) 1 k = 0 := by
  simp [kernelSum]

/- English proof (translation)
Rewrite using `[pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem neg_one_pow_two_mul (k : ℕ) : (-1 : S) ^ (2 * k) = 1 := by
  rw [pow_mul]
  simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact kernelSum_zero _ _`. Consider the case `succ k ih`. Rewrite using `[kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kernelSum_neg_one_neg_one (k : ℕ) : kernelSum (-1 : S) (-1) k = 0 := by
  induction k with
  | zero => exact kernelSum_zero _ _
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [kernelSum_zero]`. Consider the case `succ k ih`. Rewrite using `[kernelSum_succ, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kernelSum_one_neg_one (k : ℕ) : kernelSum (1 : S) (-1) k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih]
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [kernelSum_zero]`. Consider the case `succ k ih`. Rewrite using `[kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kernelSum_neg_one_one (k : ℕ) : kernelSum (-1 : S) 1 k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    push_cast
    ring

end kernelSum

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gKernel_eq_kernelSum (R : Type*) [CommRing R] (k : ℕ) :
    gKernel R k = kernelSum (X 0 : MvPolynomial (Fin 2) R) (X 1) k := rfl

/- English proof (translation)
Rewrite using `[gKernel_eq_kernelSum, map_kernelSum]`. Simplify using the standard rewrite rules.
-/
theorem eval_gKernel {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    eval ![a, b] (gKernel R k) = kernelSum a b k := by
  rw [gKernel_eq_kernelSum, map_kernelSum]
  simp

/- English proof (translation)
Use `IsHomogeneous.sum _ _ _ fun j hj => ?_` and prove the remaining obligations. Establish `hj : j < k` using `mem_range.mp hj`. Use `IsHomogeneous.sub ?_ ?_` and prove the remaining obligations. Establish `h` using `(isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))`. Rewrite `h` using `[show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega]`. Then use the resulting hypothesis.

Establish `h` using `(isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))`. Rewrite `h` using `[show 2 * j + (2 * k - 2 * j) = 2 * k by omega]`. Then use the resulting hypothesis.
-/
theorem gKernel_isHomogeneous (R : Type*) [CommRing R] (k : ℕ) :
    (gKernel R k).IsHomogeneous (2 * k) := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))
    rwa [show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega] at h
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))
    rwa [show 2 * j + (2 * k - 2 * j) = 2 * k by omega] at h

/- English proof (translation)
Introduce `R _ k`. Use `⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[gKernel_eq_kernelSum, add_mul_kernelSum]`. Rewrite using `[eval_gKernel, kernelSum_one_one]`. Rewrite using `[eval_gKernel, kernelSum_neg_one_neg_one]`.

Rewrite using `[eval_gKernel, kernelSum_one_neg_one]`. Rewrite using `[eval_gKernel, kernelSum_neg_one_one]`. Establish `h` using `add_mul_kernelSum c (-1 : R) k`. Rewrite using `[eval_gKernel, mul_comm]`. Rewrite `h` using `[neg_pow, pow_mul]`.

Rewrite `h` using `[show c + -1 = c - 1 by ring]`. Rewrite using `[h, pow_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `add_mul_kernelSum (-1 : R) c k`.

Rewrite using `[eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `add_mul_kernelSum (1 : R) c k`. Rewrite using `[eval_gKernel, mul_comm, h]`.

Simplify using the standard rewrite rules. Establish `h` using `add_mul_kernelSum c (1 : R) k`. Rewrite using `[eval_gKernel, mul_comm, h]`. Simplify using the standard rewrite rules.
-/
theorem GKernelIdentity.proof : GKernelIdentity.Statement := by
  intro R _ k
  refine ⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gKernel_eq_kernelSum, add_mul_kernelSum]
  · rw [eval_gKernel, kernelSum_one_one]
  · rw [eval_gKernel, kernelSum_neg_one_neg_one]
  · rw [eval_gKernel, kernelSum_one_neg_one]
  · rw [eval_gKernel, kernelSum_neg_one_one]
  · have h := add_mul_kernelSum c (-1 : R) k
    rw [eval_gKernel, mul_comm]
    rw [neg_pow, pow_mul] at h
    rw [show c + -1 = c - 1 by ring] at h
    rw [h, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (-1 : R) c k
    rw [eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (1 : R) c k
    rw [eval_gKernel, mul_comm, h]
    simp
  · have h := add_mul_kernelSum c (1 : R) k
    rw [eval_gKernel, mul_comm, h]
    simp

end GroundTheory.Heights₂.Heights.FlagBundles
