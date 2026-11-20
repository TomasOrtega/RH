import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TransInvOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetLat

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
The claim follows from `delta_ne HI discrNe_holds D cc hc δ hδ`.
-/
theorem delta_ne' (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne HI discrNe_holds D cc hc δ hδ

/- English proof (translation)
The claim follows from `transInv_of HI discrNe_holds sigmaStarEx_holds transInvLat_holds D`.
-/
theorem transInv_of' (HI : IdealLattice) (D : D7) : StandardLatticesGL3.transInv D :=
  transInv_of HI discrNe_holds sigmaStarEx_holds transInvLat_holds D

/- English proof (translation)
Introduce `p hp cc δ g hAt ha1 ha3`. Take `⟨hcurve, _, hδ, hLam, hOk⟩` from `hAt`. Establish `hδ0 : δ ≠ 0` using `delta_ne' HI D cc hcurve.1 δ hδ`. Take `⟨w₁, w₂, hw, hlat⟩` from `lamOf_lat HI D cc hcurve.1 δ hδ0`. Establish `hodd : ∀ z, sgStar g.abelian₂ (-z) = -sgStar g.abelian₂ z`.

Rewrite using `[hLam, hlat]`. Establish `hspec` using `Classical.epsilon_spec (sigmaStarEx_holds w₁ w₂ hw)`. Conclude with `hspec.2.2.1`. Conclude with `HP p g hOk hodd ha1 ha3`.
-/
theorem phEven_of (HI : IdealLattice) (HP : PhEvenG) (D : D7) : GL3Theta.phEven D := by
  intro p hp cc δ g hAt ha1 ha3
  obtain ⟨hcurve, _, hδ, hLam, hOk⟩ := hAt
  have hδ0 : δ ≠ 0 := delta_ne' HI D cc hcurve.1 δ hδ
  obtain ⟨w₁, w₂, hw, hlat⟩ := lamOf_lat HI D cc hcurve.1 δ hδ0

  have hodd : ∀ z, sgStar g.abelian₂ (-z) = -sgStar g.abelian₂ z := by
    rw [hLam, hlat]
    have hspec := Classical.epsilon_spec (sigmaStarEx_holds w₁ w₂ hw)
    exact hspec.2.2.1
  exact HP p g hOk hodd ha1 ha3

end Formalism.MainNotions.Ext
