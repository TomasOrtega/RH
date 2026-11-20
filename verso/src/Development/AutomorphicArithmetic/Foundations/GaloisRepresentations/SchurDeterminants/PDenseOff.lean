import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `K σ _ D hD Q hQ P hP`. Establish `hPQ : P * Q = 0`. Apply `hD` to reduce the goal to its premises. Introduce `x hx`. Distinguish the cases in `hq : eval x Q = 0`.

Rewrite using `[map_mul, hq, mul_zero]`. Rewrite using `[map_mul, hP x ⟨hx, hq⟩, zero_mul]`. Conclude with `(mul_eq_zero.1 hPQ).resolve_right hQ`.
-/
theorem UpperTheory.Gal.Schur.denseOff :
    DenseOff := by
  intro K σ _ D hD Q hQ P hP
  have hPQ : P * Q = 0 := by
    apply hD
    intro x hx
    by_cases hq : eval x Q = 0
    · rw [map_mul, hq, mul_zero]
    · rw [map_mul, hP x ⟨hx, hq⟩, zero_mul]
  exact (mul_eq_zero.1 hPQ).resolve_right hQ
