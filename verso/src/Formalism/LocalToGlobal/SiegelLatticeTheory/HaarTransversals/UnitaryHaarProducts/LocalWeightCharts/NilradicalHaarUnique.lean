import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

noncomputable section

open MeasureTheory Formalism.MainNotions.S
open scoped ENNReal

namespace WlocSk

/- English proof (translation)
Introduce `k r μ μ' hμ hμ'`. Take `⟨c, hc0, hct, hc⟩` from `HM.n_unique μ hμ`. Take `⟨c', hc0', hct', hc'⟩` from `HM.n_unique μ' hμ'`. Use `⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']`.
-/
theorem nilradical_haar_unique : NUniq := by
  intro k r μ μ' hμ hμ'
  obtain ⟨c, hc0, hct, hc⟩ := HM.n_unique μ hμ
  obtain ⟨c', hc0', hct', hc'⟩ := HM.n_unique μ' hμ'
  refine ⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩
  rw [hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']

end WlocSk
