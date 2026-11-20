import Mathlib
import Formalism.PeriodIntegrals.RowWtSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant

/- English proof (translation)
The claim follows from `PI.RWS.rowWtSpan_of_bideterminant h1 h2`.
-/
theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
