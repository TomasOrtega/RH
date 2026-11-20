import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalEqAddMulOfCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEffectiveShift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAddFirstField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByEffectiveDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorsCommute
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
The claim follows from `DivCycleMul.proof`.
-/
theorem DivCycleMul.full : DivCycleMul.Statement.{u} := DivCycleMul.proof

/- English proof (translation)
The claim follows from `DivCycleFiniteSupport.proof`.
-/
theorem DivCycleFiniteSupport.full : DivCycleFiniteSupport.Statement.{u} :=
  DivCycleFiniteSupport.proof

/- English proof (translation)
The claim follows from `SupSpanMultiHomog.proof`.
-/
theorem SupSpanMultiHomog.full : SupSpanMultiHomog.Statement.{u} := SupSpanMultiHomog.proof

/- English proof (translation)
The claim follows from `MinimalPrimeMultiHomog.proof`.
-/
theorem MinimalPrimeMultiHomog.full : MinimalPrimeMultiHomog.Statement.{u} :=
  MinimalPrimeMultiHomog.proof

/- English proof (translation)
The claim follows from `SpecialQuotDim.proof`.
-/
theorem SpecialQuotDim.full : SpecialQuotDim.Statement.{u} := SpecialQuotDim.proof

/- English proof (translation)
The claim follows from `MaximalIdealHeightFG.proof`.
-/
theorem MaximalIdealHeightFG.full : MaximalIdealHeightFG.Statement.{u} := MaximalIdealHeightFG.proof

/- English proof (translation)
The claim follows from `GenericDimBound.proof MaximalIdealHeightFG.full`.
-/
theorem GenericDimBound.full : GenericDimBound.Statement.{u} :=
  GenericDimBound.proof MaximalIdealHeightFG.full

/- English proof (translation)
The claim follows from `GenericFibProps.proof`.
-/
theorem GenericFibProps.full : GenericFibProps.Statement.{u} := GenericFibProps.proof

/- English proof (translation)
The claim follows from `GenericCycleCorresp.proof`.
-/
theorem GenericCycleCorresp.full : GenericCycleCorresp.Statement.{u} := GenericCycleCorresp.proof

/- English proof (translation)
The claim follows from `ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full GenericPieceRank.full SpecialIdealMultiHomog.full`.
-/
theorem ConservationOfNumberLE.full : ConservationOfNumberLE.Statement.{u} :=
  ConservationOfNumberLE.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full

/- English proof (translation)
The claim follows from `UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full CutByForm.full`.
-/
theorem UniformiserCase.full : UniformiserCase.Statement.{u} :=
  UniformiserCase.proof ConservationOfNumberLE.full GenericDimBound.full GenericFibProps.full
    GenericCycleCorresp.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full DimStrictDrop.full
    CutByForm.full

/- English proof (translation)
The claim follows from `ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full`.
-/
theorem ShiftByUniformiser.full : ShiftByUniformiser.Statement.{u} :=
  ShiftByUniformiser.proof DivCycleMul.full DivCycleFiniteSupport.full

/- English proof (translation)
The claim follows from `EffectiveShift.proof`.
-/
theorem EffectiveShift.full : EffectiveShift.Statement.{u} := EffectiveShift.proof

/- English proof (translation)
The claim follows from `Representative.proof DivCycleMul.full`.
-/
theorem Representative.full : Representative.Statement.{u} := Representative.proof DivCycleMul.full

/- English proof (translation)
The claim follows from `IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full FieldNumbers.HilbDegreeBound.full`.
-/
theorem IntNumAddFirst.full : IntNumAddFirst.Statement.{u} :=
  IntNumAddFirst.proof FieldNumbers.IntNumAdd.full FieldNumbers.IntNumZeroSlot.full
    FieldNumbers.HilbDegreeBound.full

/- English proof (translation)
The claim follows from `EffectiveCase.proof h₀ h₁`.
-/
theorem EffectiveCase.of_steps (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} :=
  EffectiveCase.proof h₀ h₁

/- English proof (translation)
The claim follows from `CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full ShiftByUniformiser.full EffectiveShift.full`.
-/
theorem CutByEffectiveDivisor.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} :=
  CutByEffectiveDivisor.proof (EffectiveCase.of_steps h₀ h₁) UniformiserCase.full
    ShiftByUniformiser.full EffectiveShift.full

/- English proof (translation)
The claim follows from `VerticalDivisorsCommute.proof (CutByEffectiveDivisor.of_steps h₀ h₁) Representative.full IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full`.
-/
theorem VerticalDivisorsCommute.of_steps (h₀ : NoCommonComponentCase.Statement.{u})
    (h₁ : CommonFactorInduction.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} :=
  VerticalDivisorsCommute.proof (CutByEffectiveDivisor.of_steps h₀ h₁) Representative.full
    IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full
    SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full
    DimStrictDrop.full

end GroundTheory.Heights₂.Heights.NumbersDVR
