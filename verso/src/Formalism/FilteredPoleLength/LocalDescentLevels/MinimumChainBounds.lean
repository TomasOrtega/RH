import Formalism.FilteredPoleLength.ReducedBasisBounds.AlternatingBinomial

namespace Formalism.LatticeBaseChangeAlt

open Real

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hx : 0 ≤ x` using `hy.trans hyx`.

Establish `hxy : 0 ≤ x - y` using `sub_nonneg.2 hyx`. Establish `hMn : 0 ≤ M ^ n` using `pow_nonneg (by linarith) n`. Establish `hyn : y ^ n ≤ M ^ n` using `by first`. Consider the case `exact pow_le_pow_left hy (hyx.trans hxM) n`. Consider the case `exact pow_le_pow_left₀ hy (hyx.trans hxM) n`.

Consider the case `(gcongr <;> linarith)`. Establish `hMn1 : M ^ n ≤ M ^ (n + 1)`. Rewrite using `[pow_succ]`. Use polynomial arithmetic with `[mul_nonneg hMn (sub_nonneg.2 hM)]`. Establish `h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n)` using `mul_le_mul_of_nonneg_left ih hx`.

Establish `h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n)` using `mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)`. Establish `h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1)` using `mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy`. Establish `e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n` using `by ring`. Establish `e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1)` using `by ring`. Rewrite using `[e]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem pow_sub_pow_le_mul_sub_mul_pow {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, x ^ n - y ^ n ≤ n * (x - y) * M ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    have hyn : y ^ n ≤ M ^ n := by
      first
      | exact pow_le_pow_left hy (hyx.trans hxM) n
      | exact pow_le_pow_left₀ hy (hyx.trans hxM) n
      | (gcongr <;> linarith)
    have hMn1 : M ^ n ≤ M ^ (n + 1) := by
      rw [pow_succ]; nlinarith [mul_nonneg hMn (sub_nonneg.2 hM)]
    have h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n) := mul_le_mul_of_nonneg_left ih hx
    have h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n) :=
      mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)
    have h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1) := by ring
    rw [e]
    push_cast
    linarith

/- English proof (translation)
Introduce `i c ε hε hε1`. Establish `h2 : (0 : ℝ) ≤ 2 ^ c` using `by positivity`. Establish `hM : (1 : ℝ) ≤ 2 ^ c + 1` using `by linarith`. Establish `key` using `pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε) (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i`. Establish `e : (2 : ℝ) ^ c + ε - 2 ^ c = ε` using `by ring`.

Rewrite `key` using `[e]`. Rewrite using `[pow_mul]`. Conclude with `key`.
-/
theorem detProductRest : DetProductRest := by
  intro i c ε hε hε1
  have h2 : (0 : ℝ) ≤ 2 ^ c := by positivity
  have hM : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
  have key := pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε)
    (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i
  have e : (2 : ℝ) ^ c + ε - 2 ^ c = ε := by ring
  rw [e] at key
  rw [pow_mul]
  exact key

end Formalism.LatticeBaseChangeAlt
