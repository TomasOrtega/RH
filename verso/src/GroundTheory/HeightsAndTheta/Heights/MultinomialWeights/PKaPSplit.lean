import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

/- English proof (translation)
Introduce `d p φ hp _ hs τ`. Establish `h2 : ∀ n : ℕ, ((φ ^ (n + 1)) (τ, false)).2 = false`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hs τ`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', Equiv.Perm.mul_apply]`. Establish `e : (φ ^ (n + 1)) (τ, false) = (((φ ^ (n + 1)) (τ, false)).1, false)` using `Prod.ext rfl ih`. Rewrite using `[e]`. Conclude with `hs _`.

Establish `hterm : ∀ n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) = (d.j : ℝ) * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n)`. Introduce `n`. Simplify using `only [rankLie, h2 n, Bool.false_eq_true, if_false]`. Rewrite using `[pow_succ, mul_inv, inv_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hr0 : 0 ≤ (p : ℝ)⁻¹` using `by positivity`. Establish `hr1 : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hp1`. Establish `hpm : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `hp0 : (p : ℝ) ≠ 0` using `by linarith`.

Unfold `kaP`. Rewrite using `[tsum_congr hterm, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]`. Establish `e1 : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p` using `by field_simp`. Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem KaPSplit.proof : KaPSplit.Statement := by
  intro d p φ hp _ hs τ
  have h2 : ∀ n : ℕ, ((φ ^ (n + 1)) (τ, false)).2 = false := by
    intro n
    induction n with
    | zero => simpa using hs τ
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have e : (φ ^ (n + 1)) (τ, false) = (((φ ^ (n + 1)) (τ, false)).1, false) :=
        Prod.ext rfl ih
      rw [e]
      exact hs _
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) =
      (d.j : ℝ) * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n) := by
    intro n
    simp only [rankLie, h2 n, Bool.false_eq_true, if_false]
    rw [pow_succ, mul_inv, inv_pow]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  unfold kaP
  rw [tsum_congr hterm, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have e1 : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [e1]
  field_simp

end GroundTheory.Heights₂.Heights.TheoremB
