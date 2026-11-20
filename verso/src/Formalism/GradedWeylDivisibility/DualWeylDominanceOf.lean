import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRowWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylSat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMap
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylIntRat
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylLeDual
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantDominance
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylMul
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowNuSum
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockHerm
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockWeightOrth
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockSubAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockRowAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DomPow
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockDiagBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bidetMem : BideterminantMem := bideterminantMem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwMem : HWMem := highestWeightVectorMem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwNe : HWNe := highestWeightVectorNeZero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Proceed by induction.

Treat this case separately. Treat this case separately.
-/
theorem weylLeDual : WeylLeDual := by
  intro R _ r n hn ν hν
  unfold weyl
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact hwMem R r n hn ν hν
  | cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bidetDominance : BideterminantDominance := bideterminantDominance
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hwRaise : HWRaise := highestWeightVectorRaising
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowNuSum : RowNuSum := rowPartSum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockPos : FockPos := fischerInnerPos
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem domPow : DomPow := dominancePowerProduct_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
