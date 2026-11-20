import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem filtration_criterion_of : LemmaA → FiltrationGenericPointCriterion :=
  fun hA n _ M CF pi hpi F _ x => mem_span_standard_iff_proj_zero hA CF pi hpi F x

end Formalism.InvariantFactorPaths.ColumnFamilies
