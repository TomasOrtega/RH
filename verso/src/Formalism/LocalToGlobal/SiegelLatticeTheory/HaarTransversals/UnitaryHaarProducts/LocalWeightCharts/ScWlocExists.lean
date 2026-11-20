import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfNilpotentChart
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NChartP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem scWlocExists (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : Formalism.L2.SG.SplitPrimeNormLemmas.WlocExists :=
  WlocSk.scWlocExists_of_chart WlocSk.nilpotent_chart_exists hR
