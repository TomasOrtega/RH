import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueLocOfFibCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthogonalProjections

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

/- English proof (translation)
The claim follows from `glueLoc_of_fibCount fibre_counting_holds`.
-/
theorem local_gluing_holds : GlueLoc :=
  glueLoc_of_fibCount fibre_counting_holds

end Formalism.L2.SG.Pf.Cnt
