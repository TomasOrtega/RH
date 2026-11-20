import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

/- English proof (translation)
Introduce `X D g ⟨C, hC⟩ hD`. Establish `iter : ∀ (k : ℕ) (x : X), g (D^[k] x) = 4 ^ k * g x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `x`. Rewrite using `[Function.iterate_succ_apply', hD, ih, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.zero_apply]`. Assume the negation of the conclusion as `hx`. Establish `hpos : 0 < |g x|` using `abs_pos.mpr hx`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (C / |g x|) (by norm_num : (1 : ℝ) < 4)`.

Establish `hle : (4 : ℝ) ^ k * |g x| ≤ C`. Use `hC (D^[k] x)` as an intermediate fact. Rewrite `this` using `[iter, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k)]`. Then use the resulting hypothesis. Establish `: C < (4 : ℝ) ^ k * |g x|` using `(div_lt_iff₀ hpos).mp hk`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BoundedHomogeneousZero.proof : BoundedHomogeneousZero.Statement.{u} := by
  intro X D g ⟨C, hC⟩ hD

  have iter : ∀ (k : ℕ) (x : X), g (D^[k] x) = 4 ^ k * g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hD, ih, pow_succ]
      ring
  funext x
  simp only [Pi.zero_apply]
  by_contra hx
  have hpos : 0 < |g x| := abs_pos.mpr hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / |g x|) (by norm_num : (1 : ℝ) < 4)
  have hle : (4 : ℝ) ^ k * |g x| ≤ C := by
    have := hC (D^[k] x)
    rwa [iter, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k)] at this
  have : C < (4 : ℝ) ^ k * |g x| := (div_lt_iff₀ hpos).mp hk
  linarith

end GroundTheory.Heights₂.Heights
