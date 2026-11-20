import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.UniformRestrictionOfEnergy
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula
import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.RankOneTermInvariant

namespace Formalism.MainStatements.RowRest

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem uniqOfPin : UniqOfPin := fun _ _ _ _ C hB u u' νl hP => use₇ C hB u u' νl hP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniform_restriction_of_finite_energy (hE : EnergyFin) : Formalism.L2.SG.Pf.ThmBChain6.AmplitudeBoundsAllChoicesUniform :=
  uniform_restriction_of_energy covariance_formula uniqOfPin hE

end Formalism.MainStatements.RowRest
