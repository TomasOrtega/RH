import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral

/- English proof (translation)
The claim follows from `PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ`.
-/
theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
