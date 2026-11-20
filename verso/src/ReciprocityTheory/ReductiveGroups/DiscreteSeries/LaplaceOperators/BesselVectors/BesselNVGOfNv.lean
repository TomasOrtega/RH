import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.BesselNV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem bAtTarget_of (hNV : NVStatement) : BAtTargetStatement := by
  intro k r z c u v b h hS
  obtain ⟨hk, -, -, -, -, -, hHC, hI, hH, hL, hG⟩ := hS
  exact hNV k r u v b h hk hHC hI hH hL hG

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem besselNVG_of_nv (hNV : NVStatement) : TopNV.BesselNVG :=
  TopNV.besselNVG_of (bAtTarget_of hNV) (sigZero fun m => S7.psiAll (n := m))

end ReciprocityTheory.ChartRestriction.DS.Lap.TopFinal
