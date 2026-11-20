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
The claim follows from `map_slope_mu`.
-/
theorem mapMu : MapMu := map_slope_mu
/- English proof (translation)
The claim follows from `scale_sandwich_bound`.
-/
theorem scaleSandwich : ScaleSandwich := scale_sandwich_bound
/- English proof (translation)
The claim follows from `orthogonal_sum_slope`.
-/
theorem orthSum : OrthSum := orthogonal_sum_slope
/- English proof (translation)
The claim follows from `power_slope_mu`.
-/
theorem powMu : PowMu := power_slope_mu
/- English proof (translation)
The claim follows from `divisor_bounds_first`.
-/
theorem boundsI : BoundsI := divisor_bounds_first
/- English proof (translation)
The claim follows from `boundsIVal_of boundsI`.
-/
theorem boundsIVal : BoundsIVal := boundsIVal_of boundsI
/- English proof (translation)
The claim follows from `orthogonal_sandwich_bound`.
-/
theorem orthSandwich : OrthSandwich := orthogonal_sandwich_bound
/- English proof (translation)
The claim follows from `transferPart_of mapMu powMu`.
-/
theorem transferPart : TransferPart := transferPart_of mapMu powMu
/- English proof (translation)
The claim follows from `transferMuMax_of scaleSandwich orthSum powMu`.
-/
theorem transferMuMax : TransferMuMax := transferMuMax_of scaleSandwich orthSum powMu
/- English proof (translation)
The claim follows from `degreeTransferBound`.
-/
theorem transferDeg : TransferDeg := degreeTransferBound
/- English proof (translation)
The claim follows from `interlaceIdentities`.
-/
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
/- English proof (translation)
The claim follows from `capacity_constant_bound`.
-/
theorem capConst : CapConst := capacity_constant_bound
/- English proof (translation)
The claim follows from `weyl_dimension_bound`.
-/
theorem weylDimBound : WeylDimBound := weyl_dimension_bound
/- English proof (translation)
The claim follows from `branch_map_formula`.
-/
theorem branchMap : BranchMap := branch_map_formula
/- English proof (translation)
The claim follows from `xi_norm_bound`.
-/
theorem xiNorm : XiNorm := xi_norm_bound

end Formalism.BranchingDeterminantCap
