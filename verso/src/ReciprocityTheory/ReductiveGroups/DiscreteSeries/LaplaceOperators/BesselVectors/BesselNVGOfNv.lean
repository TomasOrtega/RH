import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.BesselNV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `k r z c u v b h hS`. Take `⟨hk, -, -, -, -, -, hHC, hI, hH, hL, hG⟩` from `hS`. Conclude with `hNV k r u v b h hk hHC hI hH hL hG`.
-/
theorem bAtTarget_of (hNV : NVStatement) : BAtTargetStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hHC, hI, hH, hL, hG⟩ := hS
  exact hNV k r u v b h hk hHC hI hH hL hG

/- English proof (translation)
The claim follows from `TopNV.besselNVG_of (bAtTarget_of hNV) (sigZero fun m => S7.psiAll (n := m))`.
-/
theorem besselNVG_of_nv (hNV : NVStatement) : TopNV.BesselNVG :=
  TopNV.besselNVG_of (bAtTarget_of hNV) (sigZero fun m => S7.psiAll (n := m))

end ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal
