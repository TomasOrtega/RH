import Mathlib
import Formalism.PeriodIntegrals.SSAscent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.RangeMapRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.SemisimpleOfTraceFormNondegenerate
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilpotentAscent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceFormNondegenerateBaseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ssAscent : PI.SSAscent :=
  PI.SSAscent.UnitaryGroupMassFormula.ssAscent_of
    (PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent)
    PI.SSAscent.UnitaryGroupMassFormula.traceFormNondegenerate_baseChange
    PI.SSAscent.UnitaryGroupMassFormula.semisimpleOfTraceFormNondegenerate
