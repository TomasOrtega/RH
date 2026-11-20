import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAVTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaV

namespace Formalism.FourierDecayAlt.P.CutMP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jDCapA_of_inv_toda (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_grp (jDAGrp_of_parts capelli_representation_holds hI hT hTv)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jDCapA_of_inv_todaV (hI : JDACapInv) (hTv : JDACapTodaV) : JDCapA :=
  jDCapA_of_inv_toda hI jda_capelli_toda_proof hTv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jDCapA_of_todaV (hTv : JDACapTodaV) : JDCapA := jDCapA_of_inv_todaV capelli_invariance_criterion hTv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capelli_minors_holds : JDCapA := jDCapA_of_todaV jda_capelli_toda_mirror_proof

end Formalism.FourierDecayAlt.P.CutMP
