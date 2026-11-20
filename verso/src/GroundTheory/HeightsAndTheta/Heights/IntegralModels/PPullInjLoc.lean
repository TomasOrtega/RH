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
Introduce `X f _ _ p U G hG`. Take `⟨m, hm, hpm, H⟩` from `h₁ X f p`. Use `⟨m, hm, hpm, fun n hn hmn hpn V hV => ?_⟩` and prove the remaining obligations. Apply `pullSectionOn_injective_of_app PullbackBasis.proof.{0} _ G hG V` to reduce the goal to its premises. Introduce `W hW`.

Rewrite using `[morphismRestrict_app]`. Use `(ConcreteCategory.bijective_of_isIso ((baseChange f (ZLoc p)).presheaf.map (eqToHom (image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) U W)).op)).1.comp (H n (fun h => hpn (Int.natCast_dvd_natCast.mp h)) (Int.natCast_dvd_natCast.mpr hmn) _ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hxW, rfl⟩`. Conclude with `hV (hW hxW)`.
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
