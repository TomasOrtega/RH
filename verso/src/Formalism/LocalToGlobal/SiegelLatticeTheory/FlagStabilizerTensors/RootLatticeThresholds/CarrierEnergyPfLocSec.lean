import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrameLocX

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X u u' v`. Take `⟨h, hm, hsec⟩` from `Formalism.L2.SG.RealObj.InfCut.ProductExactness.SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (Formalism.L2.SG.RealObj.InfCut.ProductExactness.frameLoc_X X u u' v) one_pos`. Conclude with `⟨h, hm, fun cv hcv => hsec cv hcv⟩`.
-/
theorem stepSecX_holds : StepSecX := by
  intro D X u u' v
  obtain ⟨h, hm, hsec⟩ := Formalism.L2.SG.RealObj.InfCut.ProductExactness.SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.frameLoc_X X u u' v) one_pos
  exact ⟨h, hm, fun cv hcv => hsec cv hcv⟩

/- English proof (translation)
The claim follows from `locRep_of_sec stepSecX_holds X u u'`.
-/
theorem locRep_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L :=
  locRep_of_sec stepSecX_holds X u u'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
