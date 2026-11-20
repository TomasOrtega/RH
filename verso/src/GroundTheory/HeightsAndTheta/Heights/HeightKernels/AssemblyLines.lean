import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexMono
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexPi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdPi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealIndexPos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProductFormula
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealStdIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramPosDef
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramDetChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesFischer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesDiagGram
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramFischerBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesExtendBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordImage
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexSplit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjIndexLower
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexLog
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotGramLog
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `LinesLatticeBasis.proof`.
-/
theorem LinesLatticeBasis.full : LinesLatticeBasis.Statement :=
  LinesLatticeBasis.proof

/- English proof (translation)
The claim follows from `LinesGenIndexDet.proof LinesLatticeBasis.full`.
-/
theorem LinesGenIndexDet.full : LinesGenIndexDet.Statement :=
  LinesGenIndexDet.proof LinesLatticeBasis.full

/- English proof (translation)
The claim follows from `LinesIsLattice.proof`.
-/
theorem LinesIsLattice.full : LinesIsLattice.Statement :=
  LinesIsLattice.proof

/- English proof (translation)
The claim follows from `LinesGenIndexTrans.proof LinesLatticeBasis.full LinesGenIndexDet.full`.
-/
theorem LinesGenIndexTrans.full : LinesGenIndexTrans.Statement :=
  LinesGenIndexTrans.proof LinesLatticeBasis.full LinesGenIndexDet.full

/- English proof (translation)
The claim follows from `LinesGenIndexMono.proof LinesGenIndexTrans.full`.
-/
theorem LinesGenIndexMono.full : LinesGenIndexMono.Statement :=
  LinesGenIndexMono.proof LinesGenIndexTrans.full

/- English proof (translation)
The claim follows from `LinesGenIndexPi.proof`.
-/
theorem LinesGenIndexPi.full : LinesGenIndexPi.Statement :=
  LinesGenIndexPi.proof

/- English proof (translation)
The claim follows from `LinesStdPi.proof`.
-/
theorem LinesStdPi.full : LinesStdPi.Statement :=
  LinesStdPi.proof

/- English proof (translation)
The claim follows from `LinesStdIndexDet.proof LinesGenIndexDet.full`.
-/
theorem LinesStdIndexDet.full : LinesStdIndexDet.Statement :=
  LinesStdIndexDet.proof LinesGenIndexDet.full

/- English proof (translation)
The claim follows from `LinesIdealIndexPos.proof LinesIsLattice.full LinesGenIndexTrans.full`.
-/
theorem LinesIdealIndexPos.full : LinesIdealIndexPos.Statement :=
  LinesIdealIndexPos.proof LinesIsLattice.full LinesGenIndexTrans.full

/- English proof (translation)
The claim follows from `LinesProductFormula.proof`.
-/
theorem LinesProductFormula.full : LinesProductFormula.Statement :=
  LinesProductFormula.proof

/- English proof (translation)
The claim follows from `LinesIdealLatticeFG.proof`.
-/
theorem LinesIdealLatticeFG.full : LinesIdealLatticeFG.Statement :=
  LinesIdealLatticeFG.proof

/- English proof (translation)
The claim follows from `LinesIdealStdIndex.proof LinesGenIndexPi.full LinesStdPi.full`.
-/
theorem LinesIdealStdIndex.full : LinesIdealStdIndex.Statement :=
  LinesIdealStdIndex.proof LinesGenIndexPi.full LinesStdPi.full

/- English proof (translation)
The claim follows from `LinesGramChange.proof`.
-/
theorem LinesGramChange.full : LinesGramChange.Statement :=
  LinesGramChange.proof

/- English proof (translation)
The claim follows from `LinesGramPosDef.proof`.
-/
theorem LinesGramPosDef.full : LinesGramPosDef.Statement :=
  LinesGramPosDef.proof

/- English proof (translation)
The claim follows from `LinesGramDetChange.proof LinesGramChange.full`.
-/
theorem LinesGramDetChange.full : LinesGramDetChange.Statement :=
  LinesGramDetChange.proof LinesGramChange.full

/- English proof (translation)
The claim follows from `LinesFischer.proof`.
-/
theorem LinesFischer.full : LinesFischer.Statement :=
  LinesFischer.proof

/- English proof (translation)
The claim follows from `LinesDiagGram.proof`.
-/
theorem LinesDiagGram.full : LinesDiagGram.Statement :=
  LinesDiagGram.proof

/- English proof (translation)
The claim follows from `LinesGramFischerBound.proof LinesGramPosDef.full LinesFischer.full LinesDiagGram.full`.
-/
theorem LinesGramFischerBound.full : LinesGramFischerBound.Statement :=
  LinesGramFischerBound.proof LinesGramPosDef.full LinesFischer.full LinesDiagGram.full

/- English proof (translation)
The claim follows from `LinesExtendBasis.proof`.
-/
theorem LinesExtendBasis.full : LinesExtendBasis.Statement :=
  LinesExtendBasis.proof

/- English proof (translation)
The claim follows from `LinesCoordDet.proof`.
-/
theorem LinesCoordDet.full : LinesCoordDet.Statement :=
  LinesCoordDet.proof

/- English proof (translation)
The claim follows from `LinesCoordImage.proof`.
-/
theorem LinesCoordImage.full : LinesCoordImage.Statement :=
  LinesCoordImage.proof

/- English proof (translation)
The claim follows from `LinesQuotIndex.proof`.
-/
theorem LinesQuotIndex.full : LinesQuotIndex.Statement :=
  LinesQuotIndex.proof

/- English proof (translation)
The claim follows from `LinesProjLattice.proof LinesIdealLatticeFG.full`.
-/
theorem LinesProjLattice.full : LinesProjLattice.Statement :=
  LinesProjLattice.proof LinesIdealLatticeFG.full

/- English proof (translation)
The claim follows from `LinesQuotIndexSplit.proof LinesQuotIndex.full LinesCoordImage.full LinesCoordDet.full LinesIsLattice.full LinesGenIndexTrans.full LinesStdIndexDet.full LinesProjLattice.full`.
-/
theorem LinesQuotIndexSplit.full : LinesQuotIndexSplit.Statement :=
  LinesQuotIndexSplit.proof LinesQuotIndex.full LinesCoordImage.full LinesCoordDet.full LinesIsLattice.full LinesGenIndexTrans.full LinesStdIndexDet.full LinesProjLattice.full

/- English proof (translation)
The claim follows from `LinesProjIndexLower.proof LinesProjLattice.full LinesIdealLatticeFG.full LinesIsLattice.full LinesGenIndexMono.full LinesIdealStdIndex.full`.
-/
theorem LinesProjIndexLower.full : LinesProjIndexLower.Statement :=
  LinesProjIndexLower.proof LinesProjLattice.full LinesIdealLatticeFG.full LinesIsLattice.full LinesGenIndexMono.full LinesIdealStdIndex.full

/- English proof (translation)
The claim follows from `LinesLineDegree.proof`.
-/
theorem LinesLineDegree.full : LinesLineDegree.Statement :=
  LinesLineDegree.proof

/- English proof (translation)
The claim follows from `LinesQuotIndexLog.proof LinesQuotIndexSplit.full LinesProjIndexLower.full LinesIdealIndexPos.full LinesProductFormula.full LinesCoordDet.full`.
-/
theorem LinesQuotIndexLog.full : LinesQuotIndexLog.Statement :=
  LinesQuotIndexLog.proof LinesQuotIndexSplit.full LinesProjIndexLower.full LinesIdealIndexPos.full LinesProductFormula.full LinesCoordDet.full

/- English proof (translation)
The claim follows from `LinesQuotGramLog.proof LinesGramDetChange.full LinesCoordDet.full LinesGramFischerBound.full LinesGramPosDef.full`.
-/
theorem LinesQuotGramLog.full : LinesQuotGramLog.Statement :=
  LinesQuotGramLog.proof LinesGramDetChange.full LinesCoordDet.full LinesGramFischerBound.full LinesGramPosDef.full

/- English proof (translation)
The claim follows from `LinesQuotDegreeBound.proof LinesExtendBasis.full LinesQuotIndexLog.full LinesQuotGramLog.full`.
-/
theorem LinesQuotDegreeBound.full : LinesQuotDegreeBound.Statement :=
  LinesQuotDegreeBound.proof LinesExtendBasis.full LinesQuotIndexLog.full LinesQuotGramLog.full

/- English proof (translation)
The claim follows from `OrthogonalLines.proof LinesQuotDegreeBound.full LinesLineDegree.full`.
-/
theorem OrthogonalLines.full : OrthogonalLines.Statement :=
  OrthogonalLines.proof LinesQuotDegreeBound.full LinesLineDegree.full

end GroundTheory.Heights₂.Heights
