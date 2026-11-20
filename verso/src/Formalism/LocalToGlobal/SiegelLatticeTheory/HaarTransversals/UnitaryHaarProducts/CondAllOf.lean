import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

namespace Formalism.L2.SG.Pf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem condAll_of_locTrDual (hL : Formalism.L2.SG.Pf.CondStd.LocTrDual) : Formalism.L2.SG.Pf.NcVal.CondAll := by
  intro F _ _ hTR ψ h1 h2 v x
  haveI := hTR
  exact CondStd.condAllTR_of hL F ψ h1 h2 v x

end Formalism.L2.SG.Pf
