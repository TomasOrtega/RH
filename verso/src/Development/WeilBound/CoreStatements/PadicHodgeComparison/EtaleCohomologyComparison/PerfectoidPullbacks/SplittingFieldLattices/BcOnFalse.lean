import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.Kh3
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.SplitField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.Transport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

/- English proof (translation)
The claim follows from `bc_loc @loc_bc @poly_tf`.
-/
theorem bcOn_true : BcOn True := bc_loc @loc_bc @poly_tf

/- English proof (translation)
The claim follows from `bc_glob @glob_bc_st bcOn_true`.
-/
theorem bcOn_false : BcOn False := bc_glob @glob_bc_st bcOn_true

/- English proof (translation)
The claim follows from `@loc_gr`.
-/
theorem kh1 : KH.LocGr := @loc_gr

/- English proof (translation)
The claim follows from `@glob_serre_st`.
-/
theorem kh2 : KH.GlobSerreSt := @glob_serre_st

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Assemble the required witnesses or components as `⟨trivial, fin_o kh1 @poly_tf kh2 kh3.2⟩`.
-/
theorem finO' : True ∧ FinO := ⟨trivial, fin_o kh1 @poly_tf kh2 kh3.2⟩

/- English proof (translation)
The claim follows from `afg_a bcOn_false finO'.2`.
-/
theorem afgA : AfgA := afg_a bcOn_false finO'.2

/- English proof (translation)
The claim follows from `lift_a afgA`.
-/
theorem liftA : LiftA := lift_a afgA

/- English proof (translation)
The claim follows from `basis_b bcOn_false @k_iso`.
-/
theorem basisB : BasisB := basis_b bcOn_false @k_iso

end CrystallineSemistableComparison.Pb
