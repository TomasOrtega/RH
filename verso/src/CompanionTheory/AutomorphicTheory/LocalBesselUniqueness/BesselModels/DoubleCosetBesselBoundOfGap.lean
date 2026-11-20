import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

namespace BM

end BM

end Formalism.MainNotions.BridgeCS3d

namespace Formalism.MainNotions.BridgeCS3dBOW

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

/- English proof (translation)
Introduce `k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq hRe hne hfin`. Establish `: CompleteSpace Vp` using `FiniteDimensional.complete ℂ Vp`. Establish `hS : Side k r ε lam h σ w z c u π μW μN μG ν` using `⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩`. Take `⟨l, hlB, hla, -⟩` from `CompanionTheory.Lime.BM.dDFormOne hJ CompanionTheory.Lime.BM.inputs k r ε lam h H σ w Vp z c u π μW μN μG ν hS`. Take `⟨κ, hκ⟩` from `bow_core hS l hla hWc hWeq hRe`.

Conclude with `⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩`.
-/
theorem besselOfW_gap (hJ : CompanionTheory.Lime.BM.UniqGap) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.complete ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := CompanionTheory.Lime.BM.dDFormOne hJ CompanionTheory.Lime.BM.inputs
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩

end Formalism.MainNotions.BridgeCS3dBOW
