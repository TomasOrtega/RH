import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg

namespace Formalism.QuantumDeterminants

/- English proof (translation)
The claim follows from `unitary_group_holds`.
-/
theorem uHGroup : UHGroup := unitary_group_holds
/- English proof (translation)
The claim follows from `unitary_conjugation_holds`.
-/
theorem uHConj : UHConj := unitary_conjugation_holds
/- English proof (translation)
The claim follows from `hermitian_pos_facts_hold`.
-/
theorem hpkFacts : HpkFacts := hermitian_pos_facts_hold
/- English proof (translation)
The claim follows from `unipotent_subgroup_holds`.
-/
theorem nSubgroup : NSubgroup := unipotent_subgroup_holds
/- English proof (translation)
The claim follows from `length_additive_holds`.
-/
theorem ellAdd : EllAdd := length_additive_holds
/- English proof (translation)
The claim follows from `additive_character_holds`.
-/
theorem psiChar : PsiChar := additive_character_holds
/- English proof (translation)
The claim follows from `unitary_weyl_normal_holds`.
-/
theorem uWNormal : UWNormal := unitary_weyl_normal_holds
/- English proof (translation)
The claim follows from `symmetric_group_holds`.
-/
theorem sGroup : SGroup := symmetric_group_holds
/- English proof (translation)
The claim follows from `diagonal_inverse_holds`.
-/
theorem dInv : DInv := diagonal_inverse_holds
/- English proof (translation)
The claim follows from `group_inverse_holds`.
-/
theorem gInv : GInv := group_inverse_holds
/- English proof (translation)
The claim follows from `group_factorization_holds`.
-/
theorem gFactor : GFactor := group_factorization_holds
/- English proof (translation)
The claim follows from `reverse_cauchy_schwarz_holds`.
-/
theorem revCS : RevCS := reverse_cauchy_schwarz_holds
/- English proof (translation)
The claim follows from `group_gram_holds`.
-/
theorem gGram : GGram := group_gram_holds
/- English proof (translation)
The claim follows from `gNonneg_of group_gram_holds`.
-/
theorem gNonneg : GNonneg := gNonneg_of group_gram_holds

end Formalism.QuantumDeterminants
