import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomInjLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsLocSectionsInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

/- English proof (translation)
Introduce `X f _ _ p U F G _ hG`. Take `⟨m, hm, hpm, H⟩` from `h₁ X f p`. Use `⟨m, hm, hpm, fun n hn hmn hpn ψ₁ ψ₂ e => ?_⟩` and prove the remaining obligations. Use `set V : X.Opens := U ⊓ invOpen f n`. Establish `hinj : ∀ W : (V : Scheme.{0}).Opens, Function.Injective ((baseChangeMap f (ZLoc p) ∣_ V).app W)`.

Introduce `W`. Rewrite using `[morphismRestrict_app]`. Use `(ConcreteCategory.bijective_of_isIso ((baseChange f (ZLoc p)).presheaf.map (eqToHom (image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) V W)).op)).1.comp (H n (fun h => hpn (Int.natCast_dvd_natCast.mp h)) (Int.natCast_dvd_natCast.mpr hmn) _ ?_)` and prove the remaining obligations. Conclude with `(V.ι_image_le W).trans inf_le_right`. Establish `hG' : IsVectorBundle ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : V ≤ U))).obj G)` using `hG.pullback_of_isOpenImmersion _`.

Use `PullbackFaithful.proof _ _ _ hinj _ _ hG' ψ₁ ψ₂ ?_` and prove the remaining obligations. Unfold `pullbackHomAlong at e`. Rewrite `e` using `[cancel_epi, cancel_mono]`. Then use the resulting hypothesis.
-/
theorem SpreadHomInjLoc.proof (h₁ : LocSectionsInj.Statement) : SpreadHomInjLoc.Statement := by
  intro X f _ _ p U F G _ hG
  obtain ⟨m, hm, hpm, H⟩ := h₁ X f p
  refine ⟨m, hm, hpm, fun n hn hmn hpn ψ₁ ψ₂ e => ?_⟩
  set V : X.Opens := U ⊓ invOpen f n
  have hinj : ∀ W : (V : Scheme.{0}).Opens,
      Function.Injective ((baseChangeMap f (ZLoc p) ∣_ V).app W) := by
    intro W
    rw [morphismRestrict_app]
    refine (ConcreteCategory.bijective_of_isIso
      ((baseChange f (ZLoc p)).presheaf.map
        (eqToHom (image_morphismRestrict_preimage (baseChangeMap f (ZLoc p)) V W)).op)).1.comp
      (H n (fun h => hpn (Int.natCast_dvd_natCast.mp h)) (Int.natCast_dvd_natCast.mpr hmn) _ ?_)
    exact (V.ι_image_le W).trans inf_le_right
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (inf_le_left : V ≤ U))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine PullbackFaithful.proof _ _ _ hinj _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
