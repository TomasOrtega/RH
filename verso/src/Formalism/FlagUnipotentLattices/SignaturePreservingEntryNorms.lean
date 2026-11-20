import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq
import Formalism.FlagUnipotentLattices.UnitSumBound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LocalIntegralStructure
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ComplexMultiplicationRoot
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ConstantProductFormula

namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torsionIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.HermitianLatticeCounting.P.card_range_nsmul_mul_card_le
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_integral_entries_of_signature_preserving : Formalism.HermitianLatticeCounting.LocalIntegralStructure.EntriesOfSignaturePreserving := Formalism.HermitianLatticeCounting.P.unipotent_upper_entries
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem perpCompl : Formalism.HermitianLatticeCounting.LocalIntegralStructure.PerpCompl := Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cofactorVec : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CofactorVec := Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zZgPreserve : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := Formalism.HermitianLatticeCounting.P.integer_group_preservation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localCongr : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := Formalism.HermitianLatticeCounting.P.local_congruence_condition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sInt : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := Formalism.HermitianLatticeCounting.P.s_integrality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmB : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := Formalism.HermitianLatticeCounting.P.theorem_B_statement

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramDetGen : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDetGen := Formalism.HermitianLatticeCounting.P.gram_determinant_general
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramDet : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDet := Formalism.HermitianLatticeCounting.P.gram_determinant_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramNondeg : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramNondeg := Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem denomNormFrac : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DenomNormFrac := Formalism.HermitianLatticeCounting.P.denominator_norm_fraction
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arithmetic_square_bound_fourth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductInequalitySq := Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arithmetic_square_bound_fifth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductPlacesInequalitySq := Formalism.HermitianLatticeCounting.P.L5_arithmetic_square

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volRatio : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolRatio := Formalism.HermitianLatticeCounting.P.volume_ratio_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem constProduct : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ConstProduct := Formalism.HermitianLatticeCounting.P.constant_product_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tcritForm : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TcritForm := Formalism.HermitianLatticeCounting.P.critical_threshold_form

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
