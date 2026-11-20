import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.LargeSmall

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

/- English proof (translation)
Introduce `Ω _ ι _ v h1 hne n`. Establish `h1' : ∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)` using `h1`. Establish `hgt : ∀ i, ∃ x, 1 < v i x` using `fun i => by`. Take `⟨x, hx⟩` from `h1' i`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx]`. Use `first`. Consider the case `exact WithZero.one_lt_exp_of_pos zero_lt_one`. Consider the case `(rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; exact zero_lt_one)`. Consider the case `exact WithZero.coe_lt_coe.2 (by decide)`.

Take `⟨x, hx⟩` from `hA Ω ι v h1' (hN Ω ι v (hL Ω ι v hgt (hP Ω ι v h1' hne))) n`. Conclude with `⟨x, hx⟩`.
-/
theorem valApprox_of (hP : PairSep) (hL : LargeSmall) (hN : NearOne) (hA : Assembly) :
    ReciprocityTheory.ChartRestriction.G.Lift.ApproxStatement := by
  intro Ω _ ι _ v h1 hne n
  have h1' : ∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ) := h1
  have hgt : ∀ i, ∃ x, 1 < v i x := fun i => by
    obtain ⟨x, hx⟩ := h1' i
    refine ⟨x, ?_⟩
    rw [hx]
    first
    | exact WithZero.one_lt_exp_of_pos zero_lt_one
    | (rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; exact zero_lt_one)
    | exact WithZero.coe_lt_coe.2 (by decide)
  obtain ⟨x, hx⟩ := hA Ω ι v h1' (hN Ω ι v (hL Ω ι v hgt (hP Ω ι v h1' hne))) n
  exact ⟨x, hx⟩

end ReciprocityTheory.ChartRestriction.G.Lift.VA
