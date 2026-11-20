import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.AnaCore

noncomputable section

namespace PI.SqfPrimeFactor.W

/- English proof (translation)
Introduce `g r hr hg`. Use `ana_main hRS g r hr hg (bigPrimes r) (fun p => ?_)` and prove the remaining obligations. Simplify using `only [bigPrimes, Finset.mem_filter, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`.

Introduce `h; exact ⟨by omega, h⟩`.
-/
theorem analytic_of (hRS : PI.PrimesDyadicRS.Claim) : Analytic := by
  intro g r hr hg
  refine ana_main hRS g r hr hg (bigPrimes r) (fun p => ?_)
  simp only [bigPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

end PI.SqfPrimeFactor.W
