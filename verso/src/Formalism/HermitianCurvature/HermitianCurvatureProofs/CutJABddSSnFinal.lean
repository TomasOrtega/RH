import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

/- English proof (translation)
The claim follows from `sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR`.
-/
theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

/- English proof (translation)
The claim follows from `jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)`.
-/
theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

/- English proof (translation)
The claim follows from `jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)`.
-/
theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
