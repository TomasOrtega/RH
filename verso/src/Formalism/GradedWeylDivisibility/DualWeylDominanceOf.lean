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
The claim follows from `bideterminantMem`.
-/
theorem bidetMem : BideterminantMem := bideterminantMem
/- English proof (translation)
The claim follows from `highestWeightVectorMem`.
-/
theorem hwMem : HWMem := highestWeightVectorMem
/- English proof (translation)
The claim follows from `highestWeightVectorNeZero`.
-/
theorem hwNe : HWNe := highestWeightVectorNeZero
/- English proof (translation)
The claim follows from `highestWeightVectorRowWeight`.
-/
theorem hwRowWeight : HWRowWeight := highestWeightVectorRowWeight
/- English proof (translation)
The claim follows from `dualWeylModuleSaturated`.
-/
theorem dualWeylSat : DualWeylSat := dualWeylModuleSaturated
/- English proof (translation)
The claim follows from `dualWeylModuleMemIff`.
-/
theorem dualWeylPoint : DualWeylPoint := dualWeylModuleMemIff
/- English proof (translation)
The claim follows from `dualWeylModuleRowActionStable`.
-/
theorem dualWeylRowStable : DualWeylRowStable := dualWeylModuleRowActionStable
/- English proof (translation)
The claim follows from `dualWeylModuleRowDividedPowerStable`.
-/
theorem rowDivStable : RowDivStable := dualWeylModuleRowDividedPowerStable
/- English proof (translation)
The claim follows from `dualWeylModuleRowGraded`.
-/
theorem dualWeylRowGraded : DualWeylRowGraded := dualWeylModuleRowGraded
/- English proof (translation)
The claim follows from `dualWeylModuleMap`.
-/
theorem dualWeylMap : DualWeylMap := dualWeylModuleMap
/- English proof (translation)
The claim follows from `dualWeylModuleIntRat`.
-/
theorem dualWeylIntRat : DualWeylIntRat := dualWeylModuleIntRat
/- English proof (translation)
Introduce `R _ r n hn ν hν`. Unfold `weyl`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Proceed by induction on `w with`.

Consider the case `nil => exact hwMem R r n hn ν hν`. Consider the case `cons x w ih => exact rowDivStable R r n ν x.1 x.2.1 x.2.2 _ ih`.
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
The claim follows from `dualWeylModuleNonDominant`.
-/
theorem dualWeylNonDom : DualWeylNonDom := dualWeylModuleNonDominant
/- English proof (translation)
The claim follows from `bideterminantDominance`.
-/
theorem bidetDominance : BideterminantDominance := bideterminantDominance
/- English proof (translation)
The claim follows from `dualWeylModuleMul`.
-/
theorem dualWeylMul : DualWeylMul := dualWeylModuleMul
/- English proof (translation)
The claim follows from `highestWeightVectorRaising`.
-/
theorem hwRaise : HWRaise := highestWeightVectorRaising
/- English proof (translation)
The claim follows from `weylModuleRowDividedPowerStable`.
-/
theorem weylRowDivStable : WeylRowDivStable := weylModuleRowDividedPowerStable
/- English proof (translation)
The claim follows from `rowPartSum`.
-/
theorem rowNuSum : RowNuSum := rowPartSum
/- English proof (translation)
The claim follows from `fischerInnerConjSymm_holds`.
-/
theorem fockHerm : FockHerm := fischerInnerConjSymm_holds
/- English proof (translation)
The claim follows from `fischerInnerPos`.
-/
theorem fockPos : FockPos := fischerInnerPos
/- English proof (translation)
The claim follows from `fischerInnerWeightOrthogonal_holds`.
-/
theorem fockWeightOrth : FockWeightOrth := fischerInnerWeightOrthogonal_holds
/- English proof (translation)
The claim follows from `fischerInnerSubstitutionAdjoint`.
-/
theorem fockSubAdj : FockSubAdj := fischerInnerSubstitutionAdjoint
/- English proof (translation)
The claim follows from `fischerInnerRowActionAdjoint`.
-/
theorem fockRowAdj : FockRowAdj := fischerInnerRowActionAdjoint
/- English proof (translation)
The claim follows from `dominancePowerProduct_holds`.
-/
theorem domPow : DomPow := dominancePowerProduct_holds
/- English proof (translation)
The claim follows from `fockDiagBound_of domPow`.
-/
theorem fockDiagBound : FockDiagBound := fockDiagBound_of domPow

end Formalism.GradedWeylDivisibility
