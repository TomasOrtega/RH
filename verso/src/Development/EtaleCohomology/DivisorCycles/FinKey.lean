import Development.EtaleCohomology.DivisorCycles.MatUnitsOf
import Development.EtaleCohomology.DivisorCycles.ConjugateIdempotents
import Development.EtaleCohomology.DivisorCycles.UnitFactorizationTheorem
import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.ZclMulPf
import Development.EtaleCohomology.DivisorCycles.TangentIndexDvd
import Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
import Development.EtaleCohomology.DivisorCycles.ExpVanPf
import Development.EtaleCohomology.DivisorCycles.UnipotentPartTrivial
import Development.EtaleCohomology.DivisorCycles.GenSpecProof
import Development.EtaleCohomology.DivisorCycles.SpecPtPf
import Development.EtaleCohomology.DivisorCycles.TorusPtPf
import Development.EtaleCohomology.DivisorCycles.DegPoly2
import Development.EtaleCohomology.DivisorCycles.TangentDegree
import Development.EtaleCohomology.DivisorCycles.CycleCount2
import Development.EtaleCohomology.DivisorCycles.SumMulSum

namespace LateralTheory.Fin.Key
/- English proof (translation)
Apply `LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of` to reduce the goal to its premises.
-/
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key`.
-/
theorem etale_idempotent_conjugacy_of_key : LateralTheory.DivDb.IdemConj := by
  apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key
/- English proof (translation)
Apply `LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of` to reduce the goal to its premises.
-/
theorem etale_unit_factorization_of_key : LateralTheory.DivDb.UnitFactorization := by
  apply LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of
/- English proof (translation)
Apply `LateralTheory.DivDb.Chain_of` to reduce the goal to its premises.
-/
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key`.
-/
theorem etale_zariski_closure_mul_closed_of_key : LateralTheory.DivDb.ZclMul := by
  apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key`.
-/
theorem etale_tangent_index_divides_of_key : LateralTheory.DivDb.TanIndex := by
  apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key`.
-/
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key`.
-/
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key`.
-/
theorem etale_unipotent_part_trivial_of_key : LateralTheory.DivDb.Unip := by
  apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key
/- English proof (translation)
Apply `LateralTheory.DivDb.GenSpecProof.GenSpec_of` to reduce the goal to its premises.
-/
theorem etale_generic_spectrum_of_key : LateralTheory.DivDb.GenSpec := by
  apply LateralTheory.DivDb.GenSpecProof.GenSpec_of
/- English proof (translation)
Apply `LateralTheory.DivDb.SpecPtPf.SpecPt_of` to reduce the goal to its premises.
-/
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key`.
-/
theorem etale_torus_point_exists_of_key : LateralTheory.DivDb.TorusPt := by
  apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key
/- English proof (translation)
Apply `LateralTheory.DivDb.DegPoly₂.DegPoly_of` to reduce the goal to its premises.
-/
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound`.
-/
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
/- English proof (translation)
Apply `LateralTheory.DivDb.CycleCount₂.CycleCount_of` to reduce the goal to its premises.
-/
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCount₂.CycleCount_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski …`.
-/
theorem etale_divisibility_key_criterion_of_components : LateralTheory.DivDb.Key := by
  apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski_closure_mul_closed_of_key | exact etale_generic_spectrum_of_key | exact etale_torus_point_exists_of_key | exact etale_tangent_degree_bound_of_key | exact etale_cycle_count_eigenvalues_of_key
/- English proof (translation)
The claim follows from `etale_divisibility_key_criterion_of_components`.
-/
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Key := etale_divisibility_key_criterion_of_components
end LateralTheory.Fin.Key
