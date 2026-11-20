import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSRatio

namespace Formalism.QuantumDeterminants

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowKInt : LowKInt := low_k_integrable_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowKDiff : LowKDiff := low_k_differentiable_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lowKDom : LowKDom := low_k_dominant_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem holLowK : HolLowK := holomorphic_low_k_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem holHC : HolHC := holomorphic_harish_chandra_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fdegPos : FdegPos := formal_degree_pos_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fdegPerm : FdegPerm := formal_degree_perm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fdegVand : FdegVand := formal_degree_vandermonde_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fdegWeyl : FdegWeyl := formal_degree_weyl_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formal_degree_unitary_facts : FormalDegreeTwoByTwo := formalDegreeTwoByTwo_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem holFdeg : HolFdeg := holomorphicFormalDegree_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capelliHW : CapelliHW := capelliHighestWeight_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capPPerm : CapPPerm := capelliPolynomialPermInvariant_holds

end Formalism.QuantumDeterminants
