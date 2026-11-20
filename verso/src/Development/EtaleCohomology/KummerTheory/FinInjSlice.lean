import Development.EtaleCohomology.KummerTheory.ForgetInjPf
import Development.EtaleCohomology.KummerTheory.InjSlicePf

namespace LateralTheory.Fin.InjSlice
/- English proof (translation)
Apply `LateralTheory.KummerTheory.ForgetInj_of` to reduce the goal to its premises.
-/
theorem etale_forget_preservesInjectiveObjects : LateralTheory.KummerTheory.ForgetInj := by
  apply LateralTheory.KummerTheory.ForgetInj_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects`.
-/
theorem etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a : LateralTheory.KummerTheory.InjSlice := by
  apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects
/- English proof (translation)
The claim follows from `etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a`.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.InjSlice := etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
end LateralTheory.Fin.InjSlice
