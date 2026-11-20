import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg

namespace Formalism.QuantumDeterminants

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uHGroup : UHGroup := unitary_group_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uHConj : UHConj := unitary_conjugation_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hpkFacts : HpkFacts := hermitian_pos_facts_hold
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nSubgroup : NSubgroup := unipotent_subgroup_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellAdd : EllAdd := length_additive_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiChar : PsiChar := additive_character_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uWNormal : UWNormal := unitary_weyl_normal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sGroup : SGroup := symmetric_group_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dInv : DInv := diagonal_inverse_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gInv : GInv := group_inverse_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gFactor : GFactor := group_factorization_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem revCS : RevCS := reverse_cauchy_schwarz_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gGram : GGram := group_gram_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gNonneg : GNonneg := gNonneg_of group_gram_holds

end Formalism.QuantumDeterminants
