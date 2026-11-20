import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NewtonRecursionPolyUnique
import Mathlib
open Finset Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.newton_recursion_poly_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNewtonRecursionPolyUnique.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.poly_eq_zero_of_newton_recursion : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  first | exact @GlobalTheory.newton_recursion_poly_unique | exact GlobalTheory.newton_recursion_poly_unique | (intros; apply GlobalTheory.newton_recursion_poly_unique <;> assumption)
