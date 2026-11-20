import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ S _ _ _ y C`. Take `⟨φ, hφ⟩` from `isExpOf_exists C`. Conclude with `⟨φ, hφ, ExpChartJet.isExpChart_of_expOf C φ hφ (hAct E H Dw l Xo c S y C φ hφ)⟩`.
-/
theorem expChartOf_of (hAct : ExpActOfSt) : ExpChartOfSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C
  obtain ⟨φ, hφ⟩ := isExpOf_exists C
  exact ⟨φ, hφ, ExpChartJet.isExpChart_of_expOf C φ hφ (hAct E H Dw l Xo c S y C φ hφ)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
