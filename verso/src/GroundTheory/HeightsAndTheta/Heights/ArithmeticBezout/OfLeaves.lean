import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeLogBound
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `sphereMeanLinear`.
-/
theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

/- English proof (translation)
The claim follows from `chowFormSwap`.
-/
theorem ChowFormSwap.full : ChowFormSwap.Statement := chowFormSwap

/- English proof (translation)
The claim follows from `gaussLemma`.
-/
theorem GaussLemma.full : GaussLemma.Statement := gaussLemma

/- English proof (translation)
The claim follows from `mahlerMul`.
-/
theorem MahlerMul.full : MahlerMul.Statement := mahlerMul

/- English proof (translation)
The claim follows from `chowHeightMul_of_mahlerMul mahlerMul`.
-/
theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

/- English proof (translation)
The claim follows from `chowHeightConst`.
-/
theorem ChowHeightConst.full : ChowHeightConst.Statement := chowHeightConst

/- English proof (translation)
The claim follows from `ConeLogBound.proof hMass hFin hInt hNull`.
-/
theorem ConeLogBound.of_leaves (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ConeLogBound.Statement :=
  ConeLogBound.proof hMass hFin hInt hNull

/- English proof (translation)
The claim follows from `BaseChangeLogBound.proof hB hAv (ConeLogBound.proof hMass hFin hInt hNull)`.
-/
theorem BaseChangeLogBound.of_leaves (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) (hMass : ConeIntegralMass.Statement)
    (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : BaseChangeLogBound.Statement :=
  BaseChangeLogBound.proof hB hAv (ConeLogBound.proof hMass hFin hInt hNull)

/- English proof (translation)
The claim follows from `ChowHeightRecursion.proof hV hA hB hAv`.
-/
theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

/- English proof (translation)
The claim follows from `chowHeightLowerBound_of (ChowHeightRecursion.proof hV hA hB hAv) hS (BaseChangeLogBound.of_leaves hB hAv hMass hFin hInt hNull) ChowHeightMul.full`.
-/
theorem ChowHeightLowerBound.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hMass : ConeIntegralMass.Statement) (hFin : ConeBallFinite.Statement)
    (hInt : ConeFsLogIntegrable.Statement) (hNull : ConeHyperplaneNull.Statement) :
    ChowHeightLowerBound.Statement :=
  chowHeightLowerBound_of (ChowHeightRecursion.proof hV hA hB hAv) hS
    (BaseChangeLogBound.of_leaves hB hAv hMass hFin hInt hNull) ChowHeightMul.full

/- English proof (translation)
The claim follows from `ChowHeightCharacterised.proof (ChowHeightRecursion.proof hV hA hB hAv) hS ChowHeightMul.full hPt`.
-/
theorem ChowHeightCharacterised.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hS : ChowFormSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement)
    (hPt : ProjPrimeHasPoint.Statement) : ChowHeightCharacterised.Statement :=
  ChowHeightCharacterised.proof (ChowHeightRecursion.proof hV hA hB hAv) hS ChowHeightMul.full hPt

end GroundTheory.Heights₂.Heights
