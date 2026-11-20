import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.InHHClassFin

/- English proof (translation)
Introduce `I τ`. Use extensionality with `a`. Use `show τ (star a) = starRingEnd ℂ (τ a)`. Conclude with `I.cm.cmUnram.2.1 τ a`.
-/
theorem sigConj : SigConj := by
  intro I τ
  ext a
  show τ (star a) = starRingEnd ℂ (τ a)
  exact I.cm.cmUnram.2.1 τ a

end PI.UnitaryGroupMassFormula.InHHClassFin
