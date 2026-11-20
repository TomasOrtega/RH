import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.WdetDegreeOfSmithRestrict
import ReciprocityTheory.DualLattices.RestrictHopfOrderLength
import ReciprocityTheory.DualLattices.BasechangeProjectorIdempotentAction
import ReciprocityTheory.DualLattices.SmithNormalFormStatement
import ReciprocityTheory.DualLattices.LengthDegreeOfWdetFrobenius

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
The claim follows from `cokernelLengthComparison_of wdetLen (wdetDegree_of_smith_restrict hS restrict_hopfOrder_length restrictedHopfOrderApproximation)`.
-/
theorem wdet_of_smith_normal_form (hS : EigenQuotientSmithStatement) : CokernelLengthComparisonStatement :=
  cokernelLengthComparison_of wdetLen (wdetDegree_of_smith_restrict hS restrict_hopfOrder_length restrictedHopfOrderApproximation)

/- English proof (translation)
The claim follows from `wdet_of_smith_normal_form smith_normal_form_statement`.
-/
theorem u6 : CokernelLengthComparisonStatement := wdet_of_smith_normal_form smith_normal_form_statement

/- English proof (translation)
The claim follows from `lengthDegree_of_wdet_frobenius u6 hU7`.
-/
theorem lengthDegree_of_frobenius (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement := lengthDegree_of_wdet_frobenius u6 hU7

end ReciprocityTheory.PGsh.Up
