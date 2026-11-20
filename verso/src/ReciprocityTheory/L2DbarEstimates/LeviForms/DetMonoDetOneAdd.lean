import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import Lemmata.DetMonotoneStarMulSelf.OneLeReDetOneAdd

namespace ReciprocityTheory.L2DbarEstimates.I

open Matrix
open scoped ComplexOrder MatrixOrder

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem maDet (n : ℕ) : DetMonoStatement n := by
  first | exact Bl.DetMonotoneStarMulSelf.goal1 .. | (apply Bl.DetMonotoneStarMulSelf.goal1 <;> assumption) | (intros; apply Bl.DetMonotoneStarMulSelf.goal1 <;> assumption)

end ReciprocityTheory.L2DbarEstimates.I
