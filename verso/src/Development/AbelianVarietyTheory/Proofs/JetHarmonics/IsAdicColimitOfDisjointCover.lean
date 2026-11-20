import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AdicColimit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

/- English proof (translation)
Take `⟨r, hr⟩ : ∃ r : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T, ∀ i, (r i).left = 𝒰.f i` from `⟨fun i => Over.homMk (𝒰.f i) rfl, fun i => rfl⟩`. Introduce `X f hf`. Establish `hfi : ∀ i, ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (𝒰.f i ≫ T.hom)) ≫ (_root_.GlobalTheory.AdicColimit.thickHom I (e + 1) (r i) ≫ f (e + 1)) = _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e`. Introduce `i e`. Rewrite using `[_root_.GlobalTheory.AdicColimit.thickMap_thickHom_assoc, hf]`.

Use `choose g hg hgu using fun i => h i X (fun e => _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e) (hfi i)`. Establish `hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Establish `: pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i)` using `(cancel_mono (𝒰.f i)).1 pullback.condition`. Rewrite using `[this]`. Use `haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := ⟨fun x => Set.disjoint_left.1 (hd i j hij) ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, rfl⟩ ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, by`. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩⟩`. Conclude with `isInitialOfIsEmpty.hom_ext _ _`.

Use `⟨𝒰.glueMorphisms g hglue, fun e => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `Scheme.Cover.hom_ext (𝒰.pullback₁ (_root_.GlobalTheory.AdicColimit.thickι I e T)) _ _ fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _ = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _`. Rewrite using `[← Category.assoc, pullback.condition, Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]`. Set `φ : pullback (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ⟶ (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I e (Over.mk (𝒰.f i ≫ T.hom))).left` to `pullback.lift (pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i)) (pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)) (by show pullback.snd _ _ ≫ 𝒰.f i ≫ T.hom = …`.

Rewrite using `[← Category.assoc, ← pullback.condition]`. Simplify using `only [Category.assoc]`. Conclude with `congrArg (fun k => pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ k) (pullback.condition (f := T.hom) (g := _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)))`. Establish `hφ₁ : φ ≫ _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (𝒰.f i ≫ T.hom)) = pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i)` using `pullback.lift_fst _ _ _`. Establish `hφ₂ : φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i) = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i)`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T`. Rewrite using `[Category.assoc, _root_.GlobalTheory.AdicColimit.thickHom_ι, ← Category.assoc, hφ₁]`. Use `erw [hr i]`. Conclude with `pullback.condition.symm`.

Establish `hw` using `Over.w ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)).map (r i))`. Express the relevant statement in the definitionally equal form `(φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) = _`. Rewrite using `[Category.assoc]`. Use `erw [hw]`. Conclude with `pullback.lift_snd _ _ _`.

Rewrite using `[← hφ₁, Category.assoc]`. Use `erw [hg i e]`. Rewrite using `[← Category.assoc, hφ₂]`. Use `𝒰.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]`.

Use `hgu i _ fun e => ?_` and prove the remaining obligations. Establish `hcomp` using `_root_.GlobalTheory.AdicColimit.thickHom_ι_assoc I e (r i) y`. Rewrite `hcomp` using `[hr]`. Rewrite using `[← hcomp, hy]`.
-/
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_of_disjoint_cover (R : Type) [CommRing R] (I : Ideal R)
    (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0})
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j)))
    (h : ∀ i, _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I T := by
  obtain ⟨r, hr⟩ : ∃ r : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T, ∀ i, (r i).left = 𝒰.f i :=
    ⟨fun i => Over.homMk (𝒰.f i) rfl, fun i => rfl⟩
  intro X f hf

  have hfi : ∀ i, ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (𝒰.f i ≫ T.hom)) ≫
      (_root_.GlobalTheory.AdicColimit.thickHom I (e + 1) (r i) ≫ f (e + 1)) = _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e := by
    intro i e
    rw [_root_.GlobalTheory.AdicColimit.thickMap_thickHom_assoc, hf]
  choose g hg hgu using fun i => h i X (fun e => _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e) (hfi i)
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) :=
        (cancel_mono (𝒰.f i)).1 pullback.condition
      rw [this]
    · haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := ⟨fun x =>
        Set.disjoint_left.1 (hd i j hij) ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, rfl⟩
          ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms g hglue, fun e => ?_, fun y hy => ?_⟩
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (_root_.GlobalTheory.AdicColimit.thickι I e T)) _ _ fun i => ?_
    change pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _ =
      pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    let φ : pullback (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ⟶
        (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I e (Over.mk (𝒰.f i ≫ T.hom))).left :=
      pullback.lift (pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i))
        (pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
        (by
          show pullback.snd _ _ ≫ 𝒰.f i ≫ T.hom = _
          rw [← Category.assoc, ← pullback.condition]
          simp only [Category.assoc]
          exact congrArg (fun k => pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ k)
            (pullback.condition (f := T.hom) (g := _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)))
    have hφ₁ : φ ≫ _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (𝒰.f i ≫ T.hom)) =
        pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := pullback.lift_fst _ _ _
    have hφ₂ : φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i) = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := by
      apply pullback.hom_ext
      · change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T =
          pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T
        rw [Category.assoc, _root_.GlobalTheory.AdicColimit.thickHom_ι, ← Category.assoc, hφ₁]
        erw [hr i]
        exact pullback.condition.symm
      · have hw := Over.w ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)).map (r i))
        change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) = _
        rw [Category.assoc]
        erw [hw]
        exact pullback.lift_snd _ _ _
    rw [← hφ₁, Category.assoc]
    erw [hg i e]
    rw [← Category.assoc, hφ₂]
  · refine 𝒰.hom_ext _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    refine hgu i _ fun e => ?_
    have hcomp := _root_.GlobalTheory.AdicColimit.thickHom_ι_assoc I e (r i) y
    rw [hr] at hcomp
    rw [← hcomp, hy]

end GlobalTheory.AdicColimit
