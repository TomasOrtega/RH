import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.InHHClassFin

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem sigConj : SigConj := by
  intro I τ
  ext a
  show τ (star a) = starRingEnd ℂ (τ a)
  exact I.cm.cmUnram.2.1 τ a

end PI.UnitaryGroupMassFormula.InHHClassFin
