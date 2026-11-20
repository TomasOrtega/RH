import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne

namespace PI.WBL.NIS

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem measSideP : MeasSideP := by
  intro k r z u Wp _ _ _ π μW μN hz hT hπ hW hN
  exact Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normIdSm_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) : Formalism.FourierDecayAlt.ThreeDimData.NormIdSm :=
  normIdSm_of hGS hGG measSideP

end PI.WBL.NIS
