import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe

namespace GlobalTheory

/- English proof (translation)
Assemble the required witnesses or components as `⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩`.
-/
theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory
