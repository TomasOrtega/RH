import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BoundsIVal
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.GoodDual
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
import Formalism.BranchSandwichDivisors.StatementJ
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.StepDiii
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean

namespace Formalism.BranchingDeterminantCap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mapMu : MapMu := map_slope_mu
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem scaleSandwich : ScaleSandwich := scale_sandwich_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthSum : OrthSum := orthogonal_sum_slope
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem powMu : PowMu := power_slope_mu
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem boundsI : BoundsI := divisor_bounds_first
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem boundsIVal : BoundsIVal := boundsIVal_of boundsI
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthSandwich : OrthSandwich := orthogonal_sandwich_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transferPart : TransferPart := transferPart_of mapMu powMu
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transferMuMax : TransferMuMax := transferMuMax_of scaleSandwich orthSum powMu
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transferDeg : TransferDeg := degreeTransferBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capConst : CapConst := capacity_constant_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylDimBound : WeylDimBound := weyl_dimension_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem branchMap : BranchMap := branch_map_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiNorm : XiNorm := xi_norm_bound

end Formalism.BranchingDeterminantCap
