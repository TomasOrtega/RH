import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.LargeSmall

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
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
