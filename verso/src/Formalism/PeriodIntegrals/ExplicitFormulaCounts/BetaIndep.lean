import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaIndependence.YliftLeOrth
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaModX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaIndep.betaIndep_of D u u' (beta_mod_iota_surjective D u u')`.
-/
theorem scalPairs_betaFree (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaFree D u u' :=
  PI.UnitaryGroupMassFormula.BetaIndep.betaIndep_of D u u' (beta_mod_iota_surjective D u u')
