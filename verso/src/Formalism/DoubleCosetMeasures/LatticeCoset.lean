import Formalism.DoubleCosetMeasures.Statement
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.DoubleCosetEqPreimage
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import Formalism.DoubleCosetMeasures.StatementZ
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.intRightInv`.
-/
theorem intRightInv : Formalism.DoubleCosetMeasures.IntRightInv := Formalism.DoubleCosetMeasures.P.intRightInv
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.intTwoSided`.
-/
theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.dosetVol`.
-/
theorem dosetVol : Formalism.DoubleCosetMeasures.DosetVol := Formalism.DoubleCosetMeasures.P.dosetVol
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.intBiInv`.
-/
theorem intBiInv : Formalism.DoubleCosetMeasures.IntBiInv := Formalism.DoubleCosetMeasures.P.intBiInv
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.uniGroup`.
-/
theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := Formalism.DoubleCosetMeasures.P.uniGroup
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.simpleAdd`.
-/
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.intInv`.
-/
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.latticeCoset`.
-/
theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := Formalism.DoubleCosetMeasures.P.latticeCoset
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.isoInv`.
-/
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.isoFinite`.
-/
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd`.
-/
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite`.
-/
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.phaseWellDef`.
-/
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.sectionBij`.
-/
theorem sectionBij : Formalism.DoubleCosetMeasures.SectionBij := Formalism.DoubleCosetMeasures.P.sectionBij
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.suppCompact`.
-/
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.haarExists`.
-/
theorem haarExists : Formalism.DoubleCosetMeasures.HaarExists := Formalism.DoubleCosetMeasures.P.haarExists
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.suppJ`.
-/
theorem suppJ : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.suppJ
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.lemmaUSplit`.
-/
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.glRed`.
-/
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.volJ`.
-/
theorem volJ : Formalism.DoubleCosetMeasures.VolJ := Formalism.DoubleCosetMeasures.P.volJ
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.volII`.
-/
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.volJadd`.
-/
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
