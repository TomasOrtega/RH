import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExistsGaugeNormalizedStabilizer
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB

namespace Formalism.L2.SG.Pf.GE

/- English proof (translation)
The claim follows from `(show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer`.
-/
theorem existsGaugeNormalizedStabilizer : ExistsGaugeMeasureForEachRank := (show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer

end Formalism.L2.SG.Pf.GE
