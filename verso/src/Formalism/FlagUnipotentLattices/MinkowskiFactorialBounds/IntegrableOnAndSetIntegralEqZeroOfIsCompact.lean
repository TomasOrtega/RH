import Formalism.FlagUnipotentLattices.BlockDistFromLows
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.InterlacingOfBlocksSecondCase

open Formalism.HermitianLatticeCounting.S8 Finset MeasureTheory Filter Topology TensorProduct

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (f : Fin 2 → ℝ) (g : ℝ) : (∑ i, f i + g) = (∑ i, f i) + g := rfl

/- English proof (translation)
Introduce `n q h hn hq0 hq`. Establish `hnR : (2 : ℝ) ≤ n` using `by exact_mod_cast hn`. Use `set s := Real.sqrt q with hs`. Use `set σ := Real.sqrt (n : ℝ) with hσ`. Establish `s0 : 0 ≤ s` using `Real.sqrt_nonneg _`.

Establish `σ0 : 0 ≤ σ` using `Real.sqrt_nonneg _`. Establish `s2 : s ^ 2 = q` using `Real.sq_sqrt hq0`. Establish `σ2 : σ ^ 2 = n` using `Real.sq_sqrt (by linarith)`. Establish `σ1 : 1 ≤ σ`. Rewrite using `[hσ]; exact Real.one_le_sqrt.2 (by linarith)`.

Establish `σn : σ ≤ n` using `by nlinarith`. Establish `hsσ : s ≤ 5 / 7 * σ`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `pow_lt_pow_left₀ hc (by positivity) (two_ne_zero)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hdiv : (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 / 2 + 1`. Use `push_cast`. Use `Nat.cast_div_le (α := ℝ) (m := n ^ 2) (n := 2)` as an intermediate fact. Move the coercions through the operations in `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `n2 : 0 ≤ (n : ℝ) ^ 2` using `by positivity`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hdiv s0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left σn n2]`.

Introduce `hh`. Establish `A : (n : ℝ) ^ 2 * s ≤ 5 / 7 * ((n : ℝ) ^ 2 * σ)` using `by nlinarith [mul_le_mul_of_nonneg_left hsσ n2]`. Establish `B : 0 ≤ (n : ℝ) ^ 2 * σ` using `by positivity`. Establish `C : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * σ` using `by nlinarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (n : ℝ) * (q * s) ≤ (n : ℝ) ^ 2 / 2 * s`. Establish `: (n : ℝ) * q ≤ (n : ℝ) ^ 2 / 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right this s0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (2 : ℝ) * s ≤ (n : ℝ) ^ 2 / 2 * s` using `by nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 by nlinarith) s0]`.

Establish `h3 : ((n : ℝ) - 1) * q ≤ (n : ℝ) ^ 2 / 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem explicit_constant_bound : ExplicitC := by
  intro n q h hn hq0 hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set s := Real.sqrt q with hs
  set σ := Real.sqrt (n : ℝ) with hσ
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have σ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have s2 : s ^ 2 = q := Real.sq_sqrt hq0
  have σ2 : σ ^ 2 = n := Real.sq_sqrt (by linarith)
  have σ1 : 1 ≤ σ := by
    rw [hσ]; exact Real.one_le_sqrt.2 (by linarith)
  have σn : σ ≤ n := by nlinarith
  have hsσ : s ≤ 5 / 7 * σ := by
    by_contra hc
    push Not at hc
    have := pow_lt_pow_left₀ hc (by positivity) (two_ne_zero)
    nlinarith
  have hdiv : (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 / 2 + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := n ^ 2) (n := 2)
    push_cast at this
    linarith
  have n2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hdiv s0]
  · nlinarith [mul_le_mul_of_nonneg_left σn n2]
  · intro hh
    have A : (n : ℝ) ^ 2 * s ≤ 5 / 7 * ((n : ℝ) ^ 2 * σ) := by nlinarith [mul_le_mul_of_nonneg_left hsσ n2]
    have B : 0 ≤ (n : ℝ) ^ 2 * σ := by positivity
    have C : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * σ := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · have : (n : ℝ) * (q * s) ≤ (n : ℝ) ^ 2 / 2 * s := by
        have : (n : ℝ) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this s0]
      nlinarith
    · have h2 : (2 : ℝ) * s ≤ (n : ℝ) ^ 2 / 2 * s := by nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 by nlinarith) s0]
      have h3 : ((n : ℝ) - 1) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
      nlinarith
    · nlinarith

def continuousTestFunctions {X : Type} [TopologicalSpace X] (𝒜 : Set (X → ℂ)) : Set C(X, ℂ) := {a | (a : X → ℂ) ∈ 𝒜}

end Formalism.HermitianLatticeCounting.P
