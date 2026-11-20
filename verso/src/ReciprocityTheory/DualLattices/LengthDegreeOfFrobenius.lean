import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.WdetDegreeOfSmithRestrict
import ReciprocityTheory.DualLattices.RestrictHopfOrderLength
import ReciprocityTheory.DualLattices.BasechangeProjectorIdempotentAction
import ReciprocityTheory.DualLattices.SmithNormalFormStatement
import ReciprocityTheory.DualLattices.LengthDegreeOfWdetFrobenius

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wdet_of_smith_normal_form (hS : EigenQuotientSmithStatement) : CokernelLengthComparisonStatement :=
  cokernelLengthComparison_of wdetLen (wdetDegree_of_smith_restrict hS restrict_hopfOrder_length restrictedHopfOrderApproximation)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem u6 : CokernelLengthComparisonStatement := wdet_of_smith_normal_form smith_normal_form_statement

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lengthDegree_of_frobenius (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement := lengthDegree_of_wdet_frobenius u6 hU7

end ReciprocityTheory.PGsh.Up
