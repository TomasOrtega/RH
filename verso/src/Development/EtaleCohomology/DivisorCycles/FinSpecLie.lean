import Development.EtaleCohomology.DivisorCycles.SpecPtPf
import Development.EtaleCohomology.DivisorCycles.SpecLiePf

namespace LateralTheory.Fin.SpecLie
/- English proof (translation)
Apply `LateralTheory.DivDb.SpecPtPf.SpecPt_of` to reduce the goal to its premises.
-/
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key`.
-/
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
/- English proof (translation)
The claim follows from `etale_spectrum_lie_algebra_instance`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
