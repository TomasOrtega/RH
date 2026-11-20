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
A detailed English derivation is pending.
-/
theorem SymplOmegaMem.full : SymplOmegaMem.Statement :=
  SymplOmegaMem.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplCons.full : SymplCons.Statement :=
  SymplCons.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplExtVecMul.full : SymplExtVecMul.Statement :=
  SymplExtVecMul.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplTwoRow.full : SymplTwoRow.Statement :=
  SymplTwoRow.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplGcd.full : SymplGcd.Statement :=
  SymplGcd.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplQuadDiag.full : SymplQuadDiag.Statement :=
  SymplQuadDiag.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplBoxVolume.full : SymplBoxVolume.Statement :=
  SymplBoxVolume.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplShortPrim.full : SymplShortPrim.Statement :=
  SymplShortPrim.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplGramMem.full : SymplGramMem.Statement :=
  SymplGramMem.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplReducePosDef.full : SymplReducePosDef.Statement :=
  SymplReducePosDef.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplReduceConj.full : SymplReduceConj.Statement :=
  SymplReduceConj.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplDetSchur.full : SymplDetSchur.Statement :=
  SymplDetSchur.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplExtMem.full : SymplExtMem.Statement :=
  SymplExtMem.proof SymplOmegaMem.full SymplCons.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplMinkowskiBox.full : SymplMinkowskiBox.Statement :=
  SymplMinkowskiBox.proof SymplBoxVolume.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplMinExists.full : SymplMinExists.Statement :=
  SymplMinExists.proof SymplQuadDiag.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplReduceMem.full : SymplReduceMem.Statement :=
  SymplReduceMem.proof SymplOmegaMem.full SymplCons.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplOrbit.full : SymplOrbit.Statement :=
  SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplMinBound.full : SymplMinBound.Statement :=
  SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplReduceStep.full : SymplReduceStep.Statement :=
  SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplFirstRow.full : SymplFirstRow.Statement :=
  SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplStep.full : SymplStep.Statement :=
  SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplDetBound.full : SymplDetBound.Statement :=
  SymplDetBound.proof SymplStep.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SymplecticReduction.full : SymplecticReduction.Statement :=
  SymplecticReduction.proof SymplStep.full SymplDetBound.full

end GroundTheory.Heights₂.Heights
