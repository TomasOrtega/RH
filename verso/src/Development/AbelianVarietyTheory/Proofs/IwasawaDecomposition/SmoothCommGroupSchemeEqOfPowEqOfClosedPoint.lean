import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocalRigid

/- English proof (translation)
Set `l : Sp A ⟶ pullback f f` to `pullback.lift a b h`. Establish `hq : (spMap c ≫ a) ≫ pullback.diagonal f = spMap c ≫ l`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, pullback.lift_fst]`. Rewrite using `[Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, pullback.lift_snd, hc]`.

Set `q : Sp κ ⟶ pullback (pullback.diagonal f) l` to `pullback.lift _ _ hq`. Establish `hmem : (IsLocalRing.closedPoint A : Sp A) ∈ Set.range (pullback.snd (pullback.diagonal f) l)`. Set `pt : Sp κ` to `IsLocalRing.closedPoint κ`. Use `⟨q pt, ?_⟩` and prove the remaining obligations. Establish `e : (q ≫ pullback.snd _ _) pt = spMap c pt` using `by rw [pullback.lift_snd]`.

Rewrite `e` using `[Scheme.Hom.comp_apply]`. Rewrite using `[e]`. Conclude with `IsLocalRing.comap_closedPoint c`. Establish `hs : Function.Surjective (pullback.snd (pullback.diagonal f) l)` using `fun p => (IsLocalRing.specializes_closedPoint (R := A) p).mem_open (pullback.snd (pullback.diagonal f) l).isOpenEmbedding.isOpen_range hmem`. Establish `: Epi (pullback.snd (pullback.diagonal f) l).base` using `(TopCat.epi_iff_surjective _).2 hs`.

Establish `: IsIso (pullback.snd (pullback.diagonal f) l)` using `IsOpenImmersion.isIso _`. Establish `hl : l = inv (pullback.snd (pullback.diagonal f) l) ≫ pullback.fst _ _ ≫ pullback.diagonal f`. Rewrite using `[pullback.condition, IsIso.inv_hom_id_assoc]`. Establish `ha : a = l ≫ pullback.fst f f` using `(pullback.lift_fst _ _ _).symm`. Establish `hb : b = l ≫ pullback.snd f f` using `(pullback.lift_snd _ _ _).symm`.

Rewrite using `[ha, hb, hl]`. Simplify using the standard rewrite rules.
-/
theorem eq_of_diagonal_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal f)] (a b : Sp A ⟶ X) (h : a ≫ f = b ≫ f)
    (κ : Type) [Field κ] (c : A →+* κ) [IsLocalHom c] (hc : spMap c ≫ a = spMap c ≫ b) : a = b := by
  let l : Sp A ⟶ pullback f f := pullback.lift a b h
  have hq : (spMap c ≫ a) ≫ pullback.diagonal f = spMap c ≫ l := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, pullback.lift_snd, hc]
  let q : Sp κ ⟶ pullback (pullback.diagonal f) l := pullback.lift _ _ hq
  have hmem : (IsLocalRing.closedPoint A : Sp A) ∈ Set.range (pullback.snd (pullback.diagonal f) l) := by
    let pt : Sp κ := IsLocalRing.closedPoint κ
    refine ⟨q pt, ?_⟩
    have e : (q ≫ pullback.snd _ _) pt = spMap c pt := by rw [pullback.lift_snd]
    rw [Scheme.Hom.comp_apply] at e
    rw [e]
    exact IsLocalRing.comap_closedPoint c
  have hs : Function.Surjective (pullback.snd (pullback.diagonal f) l) := fun p =>
    (IsLocalRing.specializes_closedPoint (R := A) p).mem_open
      (pullback.snd (pullback.diagonal f) l).isOpenEmbedding.isOpen_range hmem
  have : Epi (pullback.snd (pullback.diagonal f) l).base := (TopCat.epi_iff_surjective _).2 hs
  have : IsIso (pullback.snd (pullback.diagonal f) l) := IsOpenImmersion.isIso _
  have hl : l = inv (pullback.snd (pullback.diagonal f) l) ≫ pullback.fst _ _ ≫ pullback.diagonal f := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  have ha : a = l ≫ pullback.fst f f := (pullback.lift_fst _ _ _).symm
  have hb : b = l ≫ pullback.snd f f := (pullback.lift_snd _ _ _).symm
  rw [ha, hb, hl]
  simp

end GlobalTheory.LocalRigid

namespace GlobalTheory.LocalRigid

/- English proof (translation)
Introduce `S G _ _ hG A _ _ s k hk x y hxy κ _ c hc hxc`. Use `haveI := hc`. Set `GA` to `(Over.pullback s).obj G`. Use `haveI : Smooth GA.hom := inferInstanceAs (Smooth (pullback.snd G.hom s))`. Establish `hu : IsUnit (k : Γ(Sp A, ⊤))`.

Simplify using `using hk.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. Use `haveI het : Etale (mulN GA k).left := GrpTangent.etale_mulN GA hu`. Set `e` to `TorsionLift.ptsEquiv s G (Over.mk (𝟙 (Sp A))) s (Category.id_comp s)`. Establish `h1 : e.symm x ≫ mulN GA k = e.symm y ≫ mulN GA k`. Rewrite using `[GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← map_pow, ← map_pow, hxy]`.

Establish `h2 : (e.symm x).left ≫ (mulN GA k).left = (e.symm y).left ≫ (mulN GA k).left`. Simplify using `using congrArg CommaMorphism.left h1`. Establish `hfst : ∀ z, (e z).left = z.left ≫ pullback.fst G.hom s` using `fun z => TorsionLift.ptsEquiv_left s G _ s (Category.id_comp s) z`. Establish `h3 : spMap c ≫ (e.symm x).left = spMap c ≫ (e.symm y).left`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, ← hfst, ← hfst]`. Simplify using `using hxc`. Establish `wx` using `Over.w (e.symm x)`. Establish `wy` using `Over.w (e.symm y)`. Rewrite using `[Category.assoc, Category.assoc]`.

Conclude with `(congrArg (spMap c ≫ ·) wx).trans (congrArg (spMap c ≫ ·) wy).symm`. Establish `h4` using `eq_of_diagonal_of_closedPoint _ _ _ h2 κ c h3`. Establish `h5 : e.symm x = e.symm y` using `Over.OverMorphism.ext h4`. Simplify using `using congrArg e h5`.
-/
theorem eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  intro S G _ _ hG A _ _ s k hk x y hxy κ _ c hc hxc
  haveI := hc
  let GA := (Over.pullback s).obj G
  haveI : Smooth GA.hom := inferInstanceAs (Smooth (pullback.snd G.hom s))
  have hu : IsUnit (k : Γ(Sp A, ⊤)) := by
    simpa using hk.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  haveI het : Etale (mulN GA k).left := GrpTangent.etale_mulN GA hu
  let e := TorsionLift.ptsEquiv s G (Over.mk (𝟙 (Sp A))) s (Category.id_comp s)
  have h1 : e.symm x ≫ mulN GA k = e.symm y ≫ mulN GA k := by
    rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← map_pow, ← map_pow, hxy]
  have h2 : (e.symm x).left ≫ (mulN GA k).left = (e.symm y).left ≫ (mulN GA k).left := by
    simpa using congrArg CommaMorphism.left h1
  have hfst : ∀ z, (e z).left = z.left ≫ pullback.fst G.hom s := fun z =>
    TorsionLift.ptsEquiv_left s G _ s (Category.id_comp s) z
  have h3 : spMap c ≫ (e.symm x).left = spMap c ≫ (e.symm y).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hfst, ← hfst]
      simpa using hxc
    · have wx := Over.w (e.symm x)
      have wy := Over.w (e.symm y)
      rw [Category.assoc, Category.assoc]
      exact (congrArg (spMap c ≫ ·) wx).trans (congrArg (spMap c ≫ ·) wy).symm
  have h4 := eq_of_diagonal_of_closedPoint _ _ _ h2 κ c h3
  have h5 : e.symm x = e.symm y := Over.OverMorphism.ext h4
  simpa using congrArg e h5

end GlobalTheory.LocalRigid
