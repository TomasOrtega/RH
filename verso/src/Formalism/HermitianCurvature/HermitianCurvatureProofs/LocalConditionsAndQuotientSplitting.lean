import Formalism.HermitianCurvature.PrimeToDifferent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitPrimeToDifferent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationTypedIndependentExponent

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_facts_general : Formalism.FourierDecayAlt.S6.LatticesGeneral :=
  assemble_lattice_facts degreeFacts_statement different_power_conj_stable
    unramRelative twistedLatticeBetween twistedLatticeIndex dual_lattice_subset
    traceDualGe scaledIdealNorm covolumeIndex

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_facts_two_split_primes : Formalism.FourierDecayAlt.S6.TextLattices :=
  periodLatticeFactsSplitOfGeneral lattice_facts_general

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem least_norm_and_size_quotient : Formalism.FourierDecayAlt.S6.TextLeast :=
  ⟨least_norm_in_ideal, size_quotient_identity⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_conditions_and_quotient_splitting : Formalism.FourierDecayAlt.S6.TextLocal :=
  assemble_local_conditions different_power_conj_stable splitPrimeToDifferent localTwistedLattice
    localAwayFromLevel localisation_typed_condition twistedIsRealOrderLattice local_global_principle

end Formalism.FourierDecayAlt.P
