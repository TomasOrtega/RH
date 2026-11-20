import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocVan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.Transport
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locGr_h : KH.LocGr := loc_gr
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locVan_h : KH.LocVan := loc_van
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem polyTf_h : KH.PolyTf := poly_tf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem globSerreSt_h : KH.GlobSerreSt := glob_serre_st
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem globVanSt_h : KH.GlobVanSt := glob_van_st

end CrystallineSemistableComparison.Pb
