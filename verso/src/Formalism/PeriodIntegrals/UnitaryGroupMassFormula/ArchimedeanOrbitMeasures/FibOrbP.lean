import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfAction

noncomputable section

namespace PI.AprimeInfW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem fibOrbAt_of (hU : UnitsOpenTens) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) : FibOrbAt := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  obtain ⟨Ω₁, hΩ₁, hn, hu⟩ := nearFacts_of hU X u' ψ hT μinf νinf fibInf hP Ω a hCh
  exact ⟨Ω₁, hΩ₁, hn, fun T hT1 => fib_near rmulFacts_holds hF hC X u' ψ hT μinf νinf fibInf hP T (a T)
    (hu T hT1).1 (hCh.2.2.2 T (hΩ₁ hT1)) (hu T hT1).2⟩

end PI.AprimeInfW
