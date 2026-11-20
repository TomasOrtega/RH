import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `F _ n W hW`. Use `hW.isPrime` as an intermediate fact. Take `⟨j, hj⟩` from `hW.isRelevant`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hj` to reduce the goal to its premises. Establish `hmem : (X j : MvPolynomial (Fin n) F) ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) W)`. Introduce `x hx`. Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality.

Simplify using the standard rewrite rules. Take `⟨q, hq, hne⟩` from `hcon x hx0`. Conclude with `absurd (hx q hq) hne`. Rewrite `hmem` using `[IsPrime.vanishingIdeal_zeroLocus]`. Then use the resulting hypothesis.
-/
theorem ProjPrimeHasPoint.proof : ProjPrimeHasPoint.Statement := by
  intro F _ n W hW
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.isRelevant
  by_contra hcon
  push Not at hcon
  apply hj
  have hmem : (X j : MvPolynomial (Fin n) F) ∈
      vanishingIdeal F (zeroLocus (AlgebraicClosure F) W) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨q, hq, hne⟩ := hcon x hx0
      exact absurd (hx q hq) hne
  rwa [IsPrime.vanishingIdeal_zeroLocus] at hmem

end GroundTheory.Heights₂.Heights
