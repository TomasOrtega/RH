import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOpsIffHeckeLiftsAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Conclude with `Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by`. Take `⟨θ, t, ht, hθ⟩` from `D.sp.cm.cmUnram.2.2 P hP`. Use `⟨θ, ?_⟩` and prove the remaining obligations. Establish `: RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t` using `RingOfIntegers.ext ht.symm`.

Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
