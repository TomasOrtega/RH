import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.CuspidalMirabolic

namespace GlobalTheory

/- English proof (translation)
The claim follows from `CompanionTheory.Mirab.cuspidalMirabolic`.
-/
theorem cuspidalMirabolic_holds : GlobalTheory.Published.CuspidalMirabolic :=
  CompanionTheory.Mirab.cuspidalMirabolic

end GlobalTheory
