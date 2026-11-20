import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

/- English proof (translation)
The claim follows from `glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn`.
-/
theorem glueLoc_of_fibCount (hn : FibCount) : GlueLoc :=
  glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn

end Formalism.L2.SG.Pf.Cnt
