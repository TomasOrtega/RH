import Mathlib
import Formalism.PeriodIntegrals.VolNzeroOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.VolumeDegenerateRankOne

/- English proof (translation)
The claim follows from `PI.VolNzeroOne.W.volume_degenerate_rank_one`.
-/
theorem volumeUnipotentOne : PI.VolNzeroOne.VolumeUnipotentOneFrom := PI.VolNzeroOne.W.volume_degenerate_rank_one
