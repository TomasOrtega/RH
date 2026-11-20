import Development.EtaleCohomology.KummerTheory.LimExtHlPf
import Development.EtaleCohomology.KummerTheory.LimLHPf
import Development.EtaleCohomology.KummerTheory.LimAssemblePf
import Development.EtaleCohomology.KummerTheory.LimitPf

namespace LateralTheory.Fin.Limit
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_limit_extension_groups_henselian_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimExtHl := by
  apply LateralTheory.KummerTheory.LimExtHl_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_limit_local_homotopy_compatible_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimLH := by
  apply LateralTheory.KummerTheory.LimLHPf.LimLH_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_limit_cohomology_assembled_from_stages : LateralTheory.KummerTheory.LimAssemble := by
  apply LateralTheory.KummerTheory.LimAssemble_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_cohomology_commutes_with_inverse_limits : LateralTheory.KummerTheory.Limit := by
  apply LateralTheory.KummerTheory.Limit_of <;> first | exact etale_limit_extension_groups_henselian_in_inverse_limits_assembly | exact etale_limit_local_homotopy_compatible_in_inverse_limits_assembly | exact etale_limit_cohomology_assembled_from_stages
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Limit := etale_cohomology_commutes_with_inverse_limits
end LateralTheory.Fin.Limit
