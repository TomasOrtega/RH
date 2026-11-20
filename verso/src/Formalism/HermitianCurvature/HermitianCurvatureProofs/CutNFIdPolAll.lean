import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolQuad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop

namespace Formalism.FourierDecayAlt.P.CutBP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nfPolFormAll_of_top (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) : NFPolFormAll :=
  nfPolFormAll_of (nfPolQuadAll_of hMeas hApx) pairing_middle_all_levels_holds top_middle_all_levels_holds

end Formalism.FourierDecayAlt.P.CutBP
