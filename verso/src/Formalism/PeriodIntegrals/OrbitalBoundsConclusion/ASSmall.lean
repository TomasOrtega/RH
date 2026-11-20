import Mathlib
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.ExistsAsOfValLtOne

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.ASSmall.tiltSmall`.
-/
theorem smallSurjective : PI.ArtSch.TiltSmall := PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
