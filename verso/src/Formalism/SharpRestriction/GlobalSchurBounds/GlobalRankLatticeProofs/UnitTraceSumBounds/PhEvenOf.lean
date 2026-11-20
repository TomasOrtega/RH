import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TransInvOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetLat

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem delta_ne' (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne HI discrNe_holds D cc hc δ hδ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transInv_of' (HI : IdealLattice) (D : D7) : StandardLatticesGL3.transInv D :=
  transInv_of HI discrNe_holds sigmaStarEx_holds transInvLat_holds D

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
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
