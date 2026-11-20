import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullInjLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsLocSectionsInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullbackBasis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericPullInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem PullInjLoc.proof (h₁ : LocSectionsInj.Statement) : PullInjLoc.Statement := by
  intro X f _ _ p U G hG
  obtain ⟨m, hm, hpm, H⟩ := h₁ X f p
  refine ⟨m, hm, hpm, fun n hn hmn hpn V hV => ?_⟩
  apply pullSectionOn_injective_of_app PullbackBasis.proof.{0} _ G hG V
  intro W hW
  rw [morphismRestrict_app]
  refine (ConcreteCategory.bijective_of_isIso
    ((baseChange f (ZLoc p)).presheaf.map
      (eqToHom (image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) U W)).op)).1.comp
    (H n (fun h => hpn (Int.natCast_dvd_natCast.mp h)) (Int.natCast_dvd_natCast.mpr hmn) _ ?_)
  rintro _ ⟨x, hxW, rfl⟩
  exact hV (hW hxW)

end

end GroundTheory.Heights₂.Heights.Model
