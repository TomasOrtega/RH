import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
import Formalism.PeriodIntegrals.NUnimodLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Closed.BM

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc`.
-/
theorem CoefWeightedLoc_holds : CoefWeightedLoc := ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

/- English proof (translation)
The claim follows from `Formalism.L2.SG.BesselDiscreteSeries.besselNVGap`.
-/
theorem BesselNVGap_holds : BesselNVGap := Formalism.L2.SG.BesselDiscreteSeries.besselNVGap

/- English proof (translation)
The claim follows from `scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm`.
-/
theorem WlocExists_holds : WlocExists := scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

/- English proof (translation)
Establish `h` using `n_unimodular_local`. Introduce `k r ε e f wf z0 z c hF hc hz`. Conclude with `h k r ε e f wf z0 z c ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz`.
-/
theorem NUnimodLoc_holds : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  have h := n_unimodular_local
  intro k r ε e f wf z0 z c hF hc hz
  exact h k r ε e f wf z0 z c ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

/- English proof (translation)
The claim follows from `quotient_product_compact`.
-/
theorem QuotProdK_holds : Formalism.L2.SG.Pf.WFL.QuotProdK := quotient_product_compact

end Formalism.L2.SG.Closed.BM
