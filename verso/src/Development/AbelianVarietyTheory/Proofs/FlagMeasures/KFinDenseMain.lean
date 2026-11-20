import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPinsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFinDense

namespace GlobalTheory.KFinDenseCarrier

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kFinDense_main : Formalism.L2.SG.Pf.CarrierXAll.KFinDense :=
  GlobalTheory.KFinDenseDS.kFin_dense

instance : Fact (Formalism.L2.SG.Pf.CarrierXAll.KFinDense) := ⟨kFinDense_main⟩

end GlobalTheory.KFinDenseCarrier
