import Development.EtaleCohomology.KummerTheory.SHenCutPf

namespace LateralTheory.Fin.StrictHenselization
/- English proof (translation)
Apply `LateralTheory.KummerTheory.SHenCut.shen` to reduce the goal to its premises.
-/
theorem etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly : LateralTheory.KummerTheory.StrictHenselization := by
  apply LateralTheory.KummerTheory.SHenCut.shen
/- English proof (translation)
The claim follows from `etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly`.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.StrictHenselization := etale_strict_henselization_cohomology_stalk_in_local_homotopy_assembly
end LateralTheory.Fin.StrictHenselization
