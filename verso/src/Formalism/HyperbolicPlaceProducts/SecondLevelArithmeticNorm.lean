import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CardEqCardRangeNsmulMulCardKer
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SesquilinearDeterminantHolds
import Mathlib
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.SubgroupCount
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.OmegaPow
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.CountO
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.DedekindLFunctions

namespace Formalism.SLP.Final

/- English proof (translation)
The claim follows from `Formalism.SLP.P.card_range_nsmul_mul_card_le`.
-/
theorem torsionIndex : Formalism.SLP.TorsionIndex := Formalism.SLP.P.card_range_nsmul_mul_card_le
/- English proof (translation)
The claim follows from `Formalism.SLP.P.sesquilinear_determinant_holds`.
-/
theorem sesqDet : Formalism.SLP.SesqDet := Formalism.SLP.P.sesquilinear_determinant_holds
/- English proof (translation)
The claim follows from `Formalism.SLP.P.pow_primeFactors_length_le`.
-/
theorem omegaPow : Formalism.SLP.OmegaPow := Formalism.SLP.P.pow_primeFactors_length_le
/- English proof (translation)
The claim follows from `Formalism.SLP.P.card_submodules_of_index_le`.
-/
theorem submoduleIndexCountO : Formalism.SLP.SubmoduleIndexCountO := Formalism.SLP.P.card_submodules_of_index_le
/- English proof (translation)
The claim follows from `Formalism.SLP.P.card_submodules_le_of_dedekind`.
-/
theorem submoduleCountDed : Formalism.SLP.SubmoduleCountDed := Formalism.SLP.P.card_submodules_le_of_dedekind

end Formalism.SLP.Final
