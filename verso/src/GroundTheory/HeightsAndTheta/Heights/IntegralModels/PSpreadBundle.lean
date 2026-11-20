import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInside
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

/- English proof (translation)
Introduce `x`. Take `⟨V, -, hxV, n, s, hs⟩` from `hM (g.base x)`. Take `⟨U', hU', hxU', hU'V⟩` from `Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens (show x ∈ g ⁻¹ᵁ V from hxV)`. Establish `hle : g ''ᵁ U' ≤ V` using `(Scheme.Hom.image_mono g hU'V).trans (g.image_preimage_le V)`. Use `⟨U', hU', hxU', n, fun i => (M.presheaf.map (homOfLE hle).op).hom (s i), ?_⟩` and prove the remaining obligations.

Introduce `V' h`. Establish `hV' : g ''ᵁ V' ≤ V` using `(Scheme.Hom.image_mono g h).trans hle`. Establish `key : (fun r : Fin n → Γ(U, V') => ∑ i, r i • ((M.restrict g).presheaf.map (homOfLE h).op).hom ((M.presheaf.map (homOfLE hle).op).hom (s i))) = (fun r : Fin n → Γ(Y, g ''ᵁ V') => ∑ i, r i • (M.presheaf.map (homOfLE hV').op).hom (s i)) ∘ (fun r i => (g.appIso V').inv (r i))`. Use function extensionality and compare the values at `r`. Simplify using `only [Function.comp_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g.appIso V').inv (r i) • (M.presheaf.map (homOfLE (Scheme.Hom.image_mono g h)).op).hom ((M.presheaf.map (homOfLE hle).op).hom (s i)) = _`. Rewrite using `[← ConcreteCategory.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression. Rewrite using `[key]`.

Use `(hs _ hV').comp ?_` and prove the remaining obligations. Establish `e : Function.Bijective (g.appIso V').inv` using `ConcreteCategory.bijective_of_isIso (g.appIso V').inv`. Conclude with `⟨fun r r' hr => funext fun i => e.1 (congrFun hr i), fun r => ⟨fun i => (e.2 (r i)).choose, funext fun i => (e.2 (r i)).choose_spec⟩⟩`.
-/
theorem IsVectorBundle.restrict {U Y : Scheme.{u}} (g : U ⟶ Y) [IsOpenImmersion g] {M : Y.Modules}
    (hM : IsVectorBundle M) : IsVectorBundle (M.restrict g) := by
  intro x
  obtain ⟨V, -, hxV, n, s, hs⟩ := hM (g.base x)
  obtain ⟨U', hU', hxU', hU'V⟩ := Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens
    (show x ∈ g ⁻¹ᵁ V from hxV)
  have hle : g ''ᵁ U' ≤ V := (Scheme.Hom.image_mono g hU'V).trans (g.image_preimage_le V)
  refine ⟨U', hU', hxU', n, fun i => (M.presheaf.map (homOfLE hle).op).hom (s i), ?_⟩
  intro V' h
  have hV' : g ''ᵁ V' ≤ V := (Scheme.Hom.image_mono g h).trans hle
  have key : (fun r : Fin n → Γ(U, V') => ∑ i, r i •
      ((M.restrict g).presheaf.map (homOfLE h).op).hom
        ((M.presheaf.map (homOfLE hle).op).hom (s i))) =
      (fun r : Fin n → Γ(Y, g ''ᵁ V') => ∑ i, r i • (M.presheaf.map (homOfLE hV').op).hom (s i)) ∘
        (fun r i => (g.appIso V').inv (r i)) := by
    funext r
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (g.appIso V').inv (r i) • (M.presheaf.map (homOfLE (Scheme.Hom.image_mono g h)).op).hom
        ((M.presheaf.map (homOfLE hle).op).hom (s i)) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [key]
  refine (hs _ hV').comp ?_
  have e : Function.Bijective (g.appIso V').inv :=
    ConcreteCategory.bijective_of_isIso (g.appIso V').inv
  exact ⟨fun r r' hr => funext fun i => e.1 (congrFun hr i),
    fun r => ⟨fun i => (e.2 (r i)).choose, funext fun i => (e.2 (r i)).choose_spec⟩⟩

/- English proof (translation)
The claim follows from `(hM.restrict g).of_iso ((Scheme.Modules.restrictFunctorIsoPullback g).app M)`.
-/
theorem IsVectorBundle.pullback_of_isOpenImmersion {U Y : Scheme.{u}} (g : U ⟶ Y)
    [IsOpenImmersion g] {M : Y.Modules} (hM : IsVectorBundle M) :
    IsVectorBundle ((Scheme.Modules.pullback g).obj M) :=
  (hM.restrict g).of_iso ((Scheme.Modules.restrictFunctorIsoPullback g).app M)

/- English proof (translation)
Introduce `X f _ _ p E hE`. Take `⟨W, hW, E', hE', ⟨e⟩⟩` from `h₁ X f p E hE`. Take `⟨m, hm0, hmp, hmW⟩` from `h₂ X f p W hW`. Use `⟨m, hm0, hmp, fun n hmn hn => ?_⟩` and prove the remaining obligations. Establish `hle : invOpen f n ≤ W`.

Take `⟨k, rfl⟩` from `hmn`. Use `le_trans ?_ hmW` and prove the remaining obligations. Rewrite using `[Nat.cast_mul]`. Conclude with `invOpen_mul_le_left f m k`. Establish `comp : toInvOpen f (ZLoc p) n (isUnit_intCast_zLoc p n hn) ≫ X.homOfLE hle = toOpen f (ZLoc p) W hW`.

Rewrite using `[← cancel_mono W.ι]`. Simplify using `[Scheme.homOfLE_ι]`. Conclude with `⟨(Scheme.Modules.pullback (X.homOfLE hle)).obj E', hE'.pullback_of_isOpenImmersion _, ⟨(Scheme.Modules.pullbackComp _ (X.homOfLE hle)).app E' ≪≫ (Scheme.Modules.pullbackCongr comp).app E' ≪≫ e⟩⟩`.
-/
theorem SpreadBundle.proof (h₁ : SpreadBundleNbhd.Statement) (h₂ : InvOpenInside.Statement) :
    SpreadBundle.Statement := by
  intro X f _ _ p E hE
  obtain ⟨W, hW, E', hE', ⟨e⟩⟩ := h₁ X f p E hE
  obtain ⟨m, hm0, hmp, hmW⟩ := h₂ X f p W hW
  refine ⟨m, hm0, hmp, fun n hmn hn => ?_⟩
  have hle : invOpen f n ≤ W := by
    obtain ⟨k, rfl⟩ := hmn
    refine le_trans ?_ hmW
    rw [Nat.cast_mul]
    exact invOpen_mul_le_left f m k
  have comp : toInvOpen f (ZLoc p) n (isUnit_intCast_zLoc p n hn) ≫ X.homOfLE hle =
      toOpen f (ZLoc p) W hW := by
    rw [← cancel_mono W.ι]
    simp [Scheme.homOfLE_ι]
  exact ⟨(Scheme.Modules.pullback (X.homOfLE hle)).obj E',
    hE'.pullback_of_isOpenImmersion _,
    ⟨(Scheme.Modules.pullbackComp _ (X.homOfLE hle)).app E' ≪≫
      (Scheme.Modules.pullbackCongr comp).app E' ≪≫ e⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
