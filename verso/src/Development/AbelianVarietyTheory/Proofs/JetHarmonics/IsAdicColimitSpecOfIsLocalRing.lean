import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint

namespace GlobalTheory.AdicColimit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in

/- English proof (translation)
Establish `hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e`. Introduce `e`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ)` using `rfl`. Establish `hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) = pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)` using `fun e => rfl`. Establish `hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) = pullback.fst (Spec.map (CommRingCat.ofHom …`. Introduce `e`. Conclude with `pullback.lift_fst _ _ _`.

Establish `hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) = pullback.snd (Spec.map (CommRingCat.ofHom …`. Introduce `e`. Conclude with `pullback.lift_snd _ _ _`. Establish `hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ Spec.map (CommRingCat.ofHom φ) = pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.Recipro …` using `fun e => pullback.condition`. Establish `hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ)` using `fun e => by`.

Rewrite using `[_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]`. Take `⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶ pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧ (∀ e, s …` from `⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _, fun e => pullback.lift_snd _ _ _⟩`. Establish `hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _`. Introduce `e`. Take `⟨l, hl⟩` from `_root_.GlobalTheory.FormalPoint.exists_factor_level I φ (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)) (pullback.snd _ _) (by rw [hPV]; exact hcond e)`.

Use `⟨l, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs_fst, Category.id_comp, hl]`. Rewrite using `[← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq, ← Category.assoc, hl, Category.id_comp, hcond]`. Introduce `X f hf`.

Establish `hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e)`. Introduce `n`. Establish `hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) = s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]`.

Rewrite using `[← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd, Category.assoc, hthick, ← Category.assoc, hs_snd, hq]`. Use `show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n`. Rewrite using `[← Category.assoc, hmap, Category.assoc, hf]`.

Use `haveI := hA`. Take `⟨g, hg, hgu⟩` from `_root_.GlobalTheory.existsUnique_of_isAdicFamily hfam`. Establish `key : ∀ y : Spec (CommRingCat.of A) ⟶ X, (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔ (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n)`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy n`. Rewrite using `[← hs_fst, Category.assoc, ← hC, hy]`. Introduce `hy e`. Take `⟨l, hl⟩` from `hsec e`. Establish `h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) = l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)`.

Rewrite using `[← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]`. Rewrite using `[h1, Category.assoc, hy, ← Category.assoc, hl]`. Conclude with `Category.id_comp _`. Conclude with `⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩`.
-/
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A]
    [IsLocalRing A] (φ : R →+* A) (hA : IsAdicComplete (I.map φ) A) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  have hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e := by
    intro e
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick
    rw [← Spec.map_comp]
    rfl
  have hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ) := rfl
  have hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := fun e => rfl
  have hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := by
    intro e; exact pullback.lift_fst _ _ _
  have hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e := by
    intro e; exact pullback.lift_snd _ _ _
  have hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫
      Spec.map (CommRingCat.ofHom φ) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e :=
    fun e => pullback.condition
  have hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e =
      _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ) := fun e => by
    rw [_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e),
      (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧
      (∀ e, s e ≫ pullback.snd _ _ = _root_.GlobalTheory.FormalPoint.levelMap I φ e) :=
    ⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _,
      fun e => pullback.lift_snd _ _ _⟩
  have hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _ := by
    intro e
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.FormalPoint.exists_factor_level I φ
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
      (pullback.snd _ _) (by rw [hPV]; exact hcond e)
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hs_fst, Category.id_comp, hl]
    · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq,
        ← Category.assoc, hl, Category.id_comp, hcond]
  intro X f hf
  have hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e) := by
    intro n
    have hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) =
        s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]
      · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]
        simp only [Category.assoc]
        rw [← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd,
          Category.assoc, hthick, ← Category.assoc, hs_snd, hq]
    show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n
    rw [← Category.assoc, hmap, Category.assoc, hf]
  haveI := hA
  obtain ⟨g, hg, hgu⟩ := _root_.GlobalTheory.existsUnique_of_isAdicFamily hfam
  have key : ∀ y : Spec (CommRingCat.of A) ⟶ X,
      (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔
      (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n) := by
    intro y
    constructor
    · intro hy n
      rw [← hs_fst, Category.assoc, ← hC, hy]
    · intro hy e
      obtain ⟨l, hl⟩ := hsec e
      have h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
          l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) := by
        rw [← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]
      rw [h1, Category.assoc, hy, ← Category.assoc, hl]
      exact Category.id_comp _
  exact ⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩

end GlobalTheory.AdicColimit
