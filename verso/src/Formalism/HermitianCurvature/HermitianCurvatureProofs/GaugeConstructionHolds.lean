import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauge_construction_holds : GCore := gCore_of_rotK rotation_K_invariance_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelPlaceBuilt2_of_SSnRep (hJ : JfSmoothDS) (h : JA.SSn.SSnRep) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_rotK hJ Gauge.GC.rotation_K_invariance_holds h

end Formalism.FourierDecayAlt.P.CutMP
