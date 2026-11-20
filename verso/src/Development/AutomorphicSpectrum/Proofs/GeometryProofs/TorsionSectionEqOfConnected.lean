import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.HolTorsion in

/- English proof (translation)
Introduce `X G _ _ L c m N B y x x' ζ b₀ hN _ hB hb₀ hx hx' htor h₀ b₁ hb₁`. Set `o : X ⟶ G.left` to `(η[G] : 𝟙_ (Over X) ⟶ G).left`. Establish `ho : o ≫ G.hom = 𝟙 X` using `Over.w (η[G] : 𝟙_ (Over X) ⟶ G)`. Set `mk : G ⟶ G` to `(𝟙 G) ^ N`. Establish `hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o`.

Introduce `T u`. Establish `e₁ : u.left ≫ mk.left = (u ^ N).left`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Establish `e₂ : T.hom ≫ o = (1 : T ⟶ G).left`. Rewrite using `[Hom.one_def, Over.comp_left, Over.toUnit_left]`.

Rewrite using `[e₁, e₂]`. Conclude with `⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩`. Set `p` to `pullback.fst mk.left o`. Set `q` to `pullback.snd mk.left o`. Establish `H : IsPullback p q mk.left o` using `IsPullback.of_hasPullback _ _`.

Establish `hpq : p ≫ G.hom = q`. Rewrite using `[← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]`. Establish `hy : IsHolTo B y` using `isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm`. Take `⟨a, ha, hab⟩` from `exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀`. Take `⟨a', ha', hab'⟩` from `exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2.1) hb₀`.

Take `⟨z, hz, hzb⟩` from `exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha' (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀`. Set `T : Over X` to `Over.mk (pullback.fst q q ≫ q)`. Set `u : T ⟶ G` to `Over.homMk (pullback.fst q q ≫ p) (by show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q`. Rewrite using `[Category.assoc, hpq])`. Set `v : T ⟶ G` to `Over.homMk (pullback.snd q q ≫ p) (by show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q`.

Rewrite using `[Category.assoc, hpq, pullback.condition])`. Establish `hu : u ^ N = 1` using `(hkill T u).2 (by show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o`. Rewrite using `[Category.assoc, H.w, Category.assoc])`. Establish `hv : v ^ N = 1` using `(hkill T v).2 (by show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o`. Rewrite using `[Category.assoc, H.w, pullback.condition, Category.assoc])`.

Take `⟨e, he, -⟩` from `GlobalTheory.UU.existsUnique_cubWeil c hu hv`. Establish `hek : e.val ^ N = 1` using `congrArg Units.val he.pow_eq_one`. Establish `hpull : ∀ w ∈ B, GlobalTheory.UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e)`. Introduce `w hw`. Set `h : Over.mk (y w) ⟶ T` to `Over.homMk (z w) (by show z w ≫ pullback.fst q q ≫ q = y w`.

Rewrite using `[← Category.assoc, (hzb w hw).1, (hab w hw).2])`. Establish `e₁ : h ≫ u = x w` using `Over.OverMorphism.ext (by show z w ≫ pullback.fst q q ≫ p = _`. Rewrite using `[← Category.assoc, (hzb w hw).1, (hab w hw).1])`. Establish `e₂ : h ≫ v = x' w` using `Over.OverMorphism.ext (by show z w ≫ pullback.snd q q ≫ p = _`. Rewrite using `[← Category.assoc, (hzb w hw).2, (hab' w hw).1])`.

Use `he.comp h` as an intermediate fact. Rewrite `this` using `[e₁, e₂]`. Conclude with `this`. Establish `e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ` using `(hpull b₀ hb₀).unique h₀`. Establish `e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e` using `Units.ext ((val_map_appTop (z b₁) e.val).trans ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))`.

Use `hpull b₁ hb₁` as an intermediate fact. Rewrite `this` using `[e₁, e₀]`. Conclude with `this`.
-/
theorem cubWeil_const_of_isHolTo_family : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1 ∧ (x b).left ≫ G.hom = (x' b).left ≫ G.hom) → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → ∀ b ∈ B, GlobalTheory.UU.CubWeil c N (x b) (x' b) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ hN _ hB hb₀ hx hx' htor h₀ b₁ hb₁
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2.1) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, GlobalTheory.UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat
