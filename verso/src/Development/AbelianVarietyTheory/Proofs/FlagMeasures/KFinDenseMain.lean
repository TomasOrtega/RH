import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPinsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense

namespace GlobalTheory.KFinDenseCarrier

/- English proof (translation)
The claim follows from `GlobalTheory.KFinDenseDS.kFin_dense`.
-/
theorem kFinDense_main : Formalism.L2.SG.Pf.CarrierXAll.KFinDense :=
  GlobalTheory.KFinDenseDS.kFin_dense

instance : Fact (Formalism.L2.SG.Pf.CarrierXAll.KFinDense) := ⟨kFinDense_main⟩

end GlobalTheory.KFinDenseCarrier
