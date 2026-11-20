import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMixedDiffLinear
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTClosure
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDiffStepExpansion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTOfUnitSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTEventuallyConst
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnVanishBlock
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutPieces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeCriterion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAssociatedMultiHomogPrime
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepHilb
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrimeFiltration
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlockAdjoinPrime
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRelevantDimGe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumOfFiltration
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAssoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceFree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialPieceRank
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericPieceRank
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealSurj
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumber
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumVanish
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MixedDiffLinear.full : MixedDiffLinear.Statement := MixedDiffLinear.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegLTClosure.full : DegLTClosure.Statement := DegLTClosure.proof MixedDiffLinear.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiffStepExpansion.full : DiffStepExpansion.Statement := DiffStepExpansion.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegLTOfUnitSteps.full : DegLTOfUnitSteps.Statement :=
  DegLTOfUnitSteps.proof DiffStepExpansion.full MixedDiffLinear.full DegLTClosure.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegLTEventuallyConst.full : DegLTEventuallyConst.Statement :=
  DegLTEventuallyConst.proof MixedDiffLinear.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EventualValueFacts.full : EventualValueFacts.Statement := EventualValueFacts.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbFnVanishBlock.full : HilbFnVanishBlock.Statement.{u} := HilbFnVanishBlock.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GradedPieceQuot.full : GradedPieceQuot.Statement.{u} := GradedPieceQuot.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CutPieces.full : CutPieces.Statement.{u} := CutPieces.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbFnCut.full : HilbFnCut.Statement.{u} := HilbFnCut.proof GradedPieceQuot.full CutPieces.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultiHomogPrimeCriterion.full : MultiHomogPrimeCriterion.Statement.{u} :=
  MultiHomogPrimeCriterion.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ColonMultiHomog.full : ColonMultiHomog.Statement.{u} := ColonMultiHomog.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AssociatedMultiHomogPrime.full : AssociatedMultiHomogPrime.Statement.{u} :=
  AssociatedMultiHomogPrime.proof MultiHomogPrimeCriterion.full ColonMultiHomog.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FiltrationStepHilb.full : FiltrationStepHilb.Statement.{u} := FiltrationStepHilb.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FiltrationStepLength.full : FiltrationStepLength.Statement.{u} := FiltrationStepLength.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof AssociatedMultiHomogPrime.full FiltrationStepHilb.full
    FiltrationStepLength.full ColonMultiHomog.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultAtPrimeAtMinimal.full : MultAtPrimeAtMinimal.Statement.{u} := MultAtPrimeAtMinimal.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DimStrictDrop.full : DimStrictDrop.Statement.{u} := DimStrictDrop.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockAdjoinPrime.full : BlockAdjoinPrime.Statement.{u} := BlockAdjoinPrime.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelevantDimGe.full : RelevantDimGe.Statement.{u} := RelevantDimGe.proof BlockAdjoinPrime.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbDegBound.full : HilbDegBound.Statement.{u} :=
  HilbDegBound.proof HilbFnVanishBlock.full HilbFnCut.full PrimeFiltration.full DimStrictDrop.full
    RelevantDimGe.full DegLTClosure.full DegLTOfUnitSteps.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TopDimMinimal.full : TopDimMinimal.Statement.{u} := TopDimMinimal.proof DimStrictDrop.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumOfFiltration.full : IntNumOfFiltration.Statement.{u} :=
  IntNumOfFiltration.proof MixedDiffLinear.full DegLTEventuallyConst.full EventualValueFacts.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GradedPieceFree.full : GradedPieceFree.Statement.{u} := GradedPieceFree.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialPieceRank.full : SpecialPieceRank.Statement.{u} :=
  SpecialPieceRank.proof GradedPieceFree.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenericPieceRank.full : GenericPieceRank.Statement.{u} := GenericPieceRank.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialIdealMultiHomog.full : SpecialIdealMultiHomog.Statement.{u} :=
  SpecialIdealMultiHomog.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialIdealCorresp.full : SpecialIdealCorresp.Statement.{u} := SpecialIdealCorresp.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialIdealSurj.full : SpecialIdealSurj.Statement.{u} := SpecialIdealSurj.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialMultAt.full : SpecialMultAt.Statement.{u} := SpecialMultAt.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialCycleEval.full : SpecialCycleEval.Statement.{u} :=
  SpecialCycleEval.proof SpecialIdealCorresp.full SpecialIdealSurj.full SpecialMultAt.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpecialDimBound.full : SpecialDimBound.Statement.{u} := SpecialDimBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumVanish.full : IntNumVanish.Statement.{u} :=
  IntNumVanish.proof HilbDegBound.full HilbFnVanishBlock.full DegLTClosure.full EventualValueFacts.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumAssoc.full : IntNumAssoc.Statement.{u} :=
  IntNumAssoc.proof PrimeFiltration.full IntNumOfFiltration.full MultAtPrimeAtMinimal.full
    IntNumVanish.full TopDimMinimal.full HilbDegBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CutByForm.full : CutByForm.Statement.{u} :=
  CutByForm.proof IntNumAssoc.full HilbFnCut.full MixedDiffLinear.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConservationOfNumber.full : ConservationOfNumber.Statement.{u} :=
  ConservationOfNumber.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full SpecialDimBound.full

end GroundTheory.Heights₂.Heights.NumbersDVR
