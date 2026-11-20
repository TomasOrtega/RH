import Mathlib
import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOfSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.BasisMonomialsApply

/- English proof (translation)
The claim follows from `GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan`.
-/
theorem coeffNormLE_iff_spanNormLE_of_hasCompl : CutKW.KWsb := GenFrameSpan.genFrameSB_of_span GenFrameSpan.stepSpan
