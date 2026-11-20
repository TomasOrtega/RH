import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSRatio

namespace Formalism.QuantumDeterminants

/- English proof (translation)
The claim follows from `low_k_integrable_holds`.
-/
theorem lowKInt : LowKInt := low_k_integrable_holds
/- English proof (translation)
The claim follows from `low_k_differentiable_holds`.
-/
theorem lowKDiff : LowKDiff := low_k_differentiable_holds
/- English proof (translation)
The claim follows from `low_k_dominant_holds`.
-/
theorem lowKDom : LowKDom := low_k_dominant_holds
/- English proof (translation)
The claim follows from `holomorphic_low_k_holds`.
-/
theorem holLowK : HolLowK := holomorphic_low_k_holds
/- English proof (translation)
The claim follows from `holomorphic_harish_chandra_holds`.
-/
theorem holHC : HolHC := holomorphic_harish_chandra_holds
/- English proof (translation)
The claim follows from `formal_degree_pos_holds`.
-/
theorem fdegPos : FdegPos := formal_degree_pos_holds
/- English proof (translation)
The claim follows from `formal_degree_perm_holds`.
-/
theorem fdegPerm : FdegPerm := formal_degree_perm_holds
/- English proof (translation)
The claim follows from `formal_degree_vandermonde_holds`.
-/
theorem fdegVand : FdegVand := formal_degree_vandermonde_holds
/- English proof (translation)
The claim follows from `formal_degree_weyl_holds`.
-/
theorem fdegWeyl : FdegWeyl := formal_degree_weyl_holds
/- English proof (translation)
The claim follows from `formalDegreeShiftRatio_holds`.
-/
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
/- English proof (translation)
The claim follows from `formalDegreeTwoByTwo_holds`.
-/
theorem formal_degree_unitary_facts : FormalDegreeTwoByTwo := formalDegreeTwoByTwo_holds
/- English proof (translation)
The claim follows from `holomorphicFormalDegree_holds`.
-/
theorem holFdeg : HolFdeg := holomorphicFormalDegree_holds
/- English proof (translation)
The claim follows from `capelliHighestWeight_holds`.
-/
theorem capelliHW : CapelliHW := capelliHighestWeight_holds
/- English proof (translation)
The claim follows from `capelliPolynomialPermInvariant_holds`.
-/
theorem capPPerm : CapPPerm := capelliPolynomialPermInvariant_holds

end Formalism.QuantumDeterminants
