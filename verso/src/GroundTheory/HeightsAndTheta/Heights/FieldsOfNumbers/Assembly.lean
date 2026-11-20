import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HilbEventuallyPolyQualified
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPrimeFiltration
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyUnique
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyShift
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbIrrelevantZero
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMixedDiffConst
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumZeroSlot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbAddBlock
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPNProduct
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiProjPrime
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSplitRelDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GradedFinite.full : GradedFinite.Statement.{u} := GradedFinite.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbExactDivide.full : HilbExactDivide.Statement.{u} :=
  HilbExactDivide.proof GradedFinite.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolyOfDiffs.full : PolyOfDiffs.Statement := PolyOfDiffs.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbEventuallyPoly.full : HilbEventuallyPoly.Statement.{u} :=
  HilbEventuallyPoly.of_exactDivide_polyOfDiffs HilbExactDivide.full PolyOfDiffs.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof HilbExactDivide.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EventuallyPolyUnique.full : EventuallyPolyUnique.Statement := EventuallyPolyUnique.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EventuallyPolyShift.full : EventuallyPolyShift.Statement := EventuallyPolyShift.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbIrrelevantZero.full : HilbIrrelevantZero.Statement.{u} := HilbIrrelevantZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelevantPrimeDimGe.full : RelevantPrimeDimGe.Statement.{u} := RelevantPrimeDimGe.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbDegreeBound.full : HilbDegreeBound.Statement.{u} :=
  HilbDegreeBound.proof HilbEventuallyPoly.full HilbExactDivide.full PolyOfDiffs.full
    PrimeFiltration.full EventuallyPolyUnique.full EventuallyPolyShift.full
    HilbIrrelevantZero.full RelevantPrimeDimGe.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MixedDiffConst.full : MixedDiffConst.Statement.{u} :=
  MixedDiffConst.proof HilbDegreeBound.full HilbEventuallyPoly.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumSymm.full : IntNumSymm.Statement := IntNumSymm.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumAdd.full : IntNumAdd.Statement.{u} := IntNumAdd.proof MixedDiffConst.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumZeroSlot.full : IntNumZeroSlot.Statement.{u} :=
  IntNumZeroSlot.proof MixedDiffConst.full HilbEventuallyPoly.full HilbDegreeBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumBase.full : IntNumBase.Statement.{u} := IntNumBase.proof MixedDiffConst.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultEqualsCoeff.full : MultEqualsCoeff.Statement.{u} :=
  MultEqualsCoeff.proof PrimeFiltration.full MixedDiffConst.full RelevantPrimeDimGe.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CutRegular.full : CutRegular.Statement.{u} :=
  CutRegular.proof HilbExactDivide.full MultEqualsCoeff.full IntNumSymm.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CutRational.full : CutRational.Statement.{u} :=
  CutRational.proof CutRegular.full IntNumAdd.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DivPrincipalDegree.full : DivPrincipalDegree.Statement.{u} :=
  DivPrincipalDegree.proof CutRational.full IntNumBase.full IntNumZeroSlot.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ExistsForm.full : ExistsForm.Statement.{u} := ExistsForm.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DivCycleSupport.full : DivCycleSupport.Statement.{u} := DivCycleSupport.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumUnique.full : IntNumUnique.Statement.{u} :=
  IntNumUnique.proof CutRational.full IntNumBase.full ExistsForm.full DivCycleSupport.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumBaseChange.full : IntNumBaseChange.Statement := IntNumBaseChange.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjectionFormulaContracted.full : ProjectionFormulaContracted.Statement.{u} :=
  PFContracted.proof MixedDiffConst.full CutRational.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbAddBlock.full : HilbAddBlock.Statement.{u} := HilbAddBlock.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProductWithProjectiveSpace.full : ProductWithProjectiveSpace.Statement.{u} :=
  ProductWithProjectiveSpace.proof MixedDiffConst.full HilbAddBlock.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjectionFormulaDegree.of_divPushForward (h : DivPushForward.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} :=
  ProjectionFormulaDegree.proof CutRational.full IntNumBase.full ProjectionFormulaContracted.full h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RenameMultiHomog.full : RenameMultiHomog.Statement.{u} := RenameMultiHomog.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RenameHilbFn.full : RenameHilbFn.Statement.{u} := RenameHilbFn.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RenameIntNum.full : RenameIntNum.Statement.{u} := RenameIntNum.proof RenameHilbFn.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RenameMultiProjPrime.full : RenameMultiProjPrime.Statement.{u} :=
  RenameMultiProjPrime.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SplitRelDeg.full : SplitRelDeg.Statement.{u} := SplitRelDeg.proof

end GroundTheory.Heights₂.Heights.FieldNumbers
