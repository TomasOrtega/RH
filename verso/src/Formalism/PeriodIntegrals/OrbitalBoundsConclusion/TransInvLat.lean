import Mathlib
import Formalism.PeriodIntegrals.LatDefs
import Formalism.PeriodIntegrals.TransInvLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TranslationInvariantLattice.TransInvLatMain

/- English proof (translation)
The claim follows from `PI.TransInvLatW.transInvLat_main`.
-/
theorem translation_invariant_lattice : PI.TransInvLat := PI.TransInvLatW.transInvLat_main
