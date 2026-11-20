import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOmegaMem
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplCons
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtMem
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplExtVecMul
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplTwoRow
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGcd
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplQuadDiag
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplBoxVolume
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinkowskiBox
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplShortPrim
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplGramMem
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplFirstRow
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceMem
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceConj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetSchur
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceStep
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplStep
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `SymplOmegaMem.proof`.
-/
theorem SymplOmegaMem.full : SymplOmegaMem.Statement :=
  SymplOmegaMem.proof

/- English proof (translation)
The claim follows from `SymplCons.proof`.
-/
theorem SymplCons.full : SymplCons.Statement :=
  SymplCons.proof

/- English proof (translation)
The claim follows from `SymplExtVecMul.proof`.
-/
theorem SymplExtVecMul.full : SymplExtVecMul.Statement :=
  SymplExtVecMul.proof

/- English proof (translation)
The claim follows from `SymplTwoRow.proof`.
-/
theorem SymplTwoRow.full : SymplTwoRow.Statement :=
  SymplTwoRow.proof

/- English proof (translation)
The claim follows from `SymplGcd.proof`.
-/
theorem SymplGcd.full : SymplGcd.Statement :=
  SymplGcd.proof

/- English proof (translation)
The claim follows from `SymplQuadDiag.proof`.
-/
theorem SymplQuadDiag.full : SymplQuadDiag.Statement :=
  SymplQuadDiag.proof

/- English proof (translation)
The claim follows from `SymplBoxVolume.proof`.
-/
theorem SymplBoxVolume.full : SymplBoxVolume.Statement :=
  SymplBoxVolume.proof

/- English proof (translation)
The claim follows from `SymplShortPrim.proof`.
-/
theorem SymplShortPrim.full : SymplShortPrim.Statement :=
  SymplShortPrim.proof

/- English proof (translation)
The claim follows from `SymplGramMem.proof`.
-/
theorem SymplGramMem.full : SymplGramMem.Statement :=
  SymplGramMem.proof

/- English proof (translation)
The claim follows from `SymplReducePosDef.proof`.
-/
theorem SymplReducePosDef.full : SymplReducePosDef.Statement :=
  SymplReducePosDef.proof

/- English proof (translation)
The claim follows from `SymplReduceConj.proof`.
-/
theorem SymplReduceConj.full : SymplReduceConj.Statement :=
  SymplReduceConj.proof

/- English proof (translation)
The claim follows from `SymplDetSchur.proof`.
-/
theorem SymplDetSchur.full : SymplDetSchur.Statement :=
  SymplDetSchur.proof

/- English proof (translation)
The claim follows from `SymplExtMem.proof SymplOmegaMem.full SymplCons.full`.
-/
theorem SymplExtMem.full : SymplExtMem.Statement :=
  SymplExtMem.proof SymplOmegaMem.full SymplCons.full

/- English proof (translation)
The claim follows from `SymplMinkowskiBox.proof SymplBoxVolume.full`.
-/
theorem SymplMinkowskiBox.full : SymplMinkowskiBox.Statement :=
  SymplMinkowskiBox.proof SymplBoxVolume.full

/- English proof (translation)
The claim follows from `SymplMinExists.proof SymplQuadDiag.full`.
-/
theorem SymplMinExists.full : SymplMinExists.Statement :=
  SymplMinExists.proof SymplQuadDiag.full

/- English proof (translation)
The claim follows from `SymplReduceMem.proof SymplOmegaMem.full SymplCons.full`.
-/
theorem SymplReduceMem.full : SymplReduceMem.Statement :=
  SymplReduceMem.proof SymplOmegaMem.full SymplCons.full

/- English proof (translation)
The claim follows from `SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full`.
-/
theorem SymplOrbit.full : SymplOrbit.Statement :=
  SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full

/- English proof (translation)
The claim follows from `SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full`.
-/
theorem SymplMinBound.full : SymplMinBound.Statement :=
  SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full

/- English proof (translation)
The claim follows from `SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full`.
-/
theorem SymplReduceStep.full : SymplReduceStep.Statement :=
  SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full

/- English proof (translation)
The claim follows from `SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full`.
-/
theorem SymplFirstRow.full : SymplFirstRow.Statement :=
  SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full

/- English proof (translation)
The claim follows from `SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full`.
-/
theorem SymplStep.full : SymplStep.Statement :=
  SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full

/- English proof (translation)
The claim follows from `SymplDetBound.proof SymplStep.full`.
-/
theorem SymplDetBound.full : SymplDetBound.Statement :=
  SymplDetBound.proof SymplStep.full

/- English proof (translation)
The claim follows from `SymplecticReduction.proof SymplStep.full SymplDetBound.full`.
-/
theorem SymplecticReduction.full : SymplecticReduction.Statement :=
  SymplecticReduction.proof SymplStep.full SymplDetBound.full

end GroundTheory.Heights₂.Heights
