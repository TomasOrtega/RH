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
A detailed English derivation is pending.
-/
theorem intRightInv : Formalism.DoubleCosetMeasures.IntRightInv := Formalism.DoubleCosetMeasures.P.intRightInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dosetVol : Formalism.DoubleCosetMeasures.DosetVol := Formalism.DoubleCosetMeasures.P.dosetVol
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intBiInv : Formalism.DoubleCosetMeasures.IntBiInv := Formalism.DoubleCosetMeasures.P.intBiInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := Formalism.DoubleCosetMeasures.P.uniGroup
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := Formalism.DoubleCosetMeasures.P.latticeCoset
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sectionBij : Formalism.DoubleCosetMeasures.SectionBij := Formalism.DoubleCosetMeasures.P.sectionBij
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem haarExists : Formalism.DoubleCosetMeasures.HaarExists := Formalism.DoubleCosetMeasures.P.haarExists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem suppJ : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.suppJ
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volJ : Formalism.DoubleCosetMeasures.VolJ := Formalism.DoubleCosetMeasures.P.volJ
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
