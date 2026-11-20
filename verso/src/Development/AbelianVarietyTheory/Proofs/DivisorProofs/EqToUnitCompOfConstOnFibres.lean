import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FibreConstTorus

/- English proof (translation)
Simplify using `using Over.w (toUnit G)`.
-/
theorem toUnit_left {S : Scheme.{0}} (G : Over S) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem appTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (f ≫ g).appTop a = f.appTop (g.appTop a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

end FibreConstTorus

open FibreConstTorus in

/- English proof (translation)
Introduce `S G B _ hB q hfl hsu hqc X _ d hd`. Establish `hE : EffectiveEpi q.left` using `inferInstance`. Establish `hq : q.left ≫ B.hom = G.hom` using `Over.w q`. Establish `hbij : Function.Bijective B.hom.appTop.hom` using `globalFns_holds S B hB`. Establish `hpb` using `IsPullback.of_hasPullback q.left q.left`.

Set `Z : Over S` to `Over.mk (pullback.fst q.left q.left ≫ G.hom)`. Set `x : Z ⟶ G` to `Over.homMk (pullback.fst q.left q.left) rfl`. Set `y : Z ⟶ G` to `Over.homMk (pullback.snd q.left q.left) (by`. Express the relevant statement in the definitionally equal form `pullback.snd q.left q.left ≫ G.hom = pullback.fst q.left q.left ≫ G.hom`. Rewrite using `[← hq, pullback.condition_assoc])`.

Establish `hxy : x ≫ q = y ≫ q` using `by ext1`. Conclude with `(pullback.condition (f := q.left) (g := q.left))`. Establish `hdl : pullback.fst q.left q.left ≫ d.left = pullback.snd q.left q.left ≫ d.left` using `congrArg CommaMorphism.left (hd Z x y hxy)`. Establish `key : ∀ c : Γ((splitTorus S X).left, ⊤), (pullback.fst q.left q.left).appTop (d.left.appTop c) = (pullback.snd q.left q.left).appTop (d.left.appTop c)` using `fun c => by`. Rewrite using `[← appTop_comp_apply, ← appTop_comp_apply, hdl]`.

Take `⟨f, hf⟩ : ∃ f, f = splitTorusPointsEquiv S X G d` from `⟨_, rfl⟩`. Establish `hfv : ∀ χ : X, (f (Multiplicative.ofAdd χ)).val = d.left.appTop (charUnit S X χ).val` using `fun χ => hf ▸ splitTorusPointsEquiv_val S X G d χ`. Set `incl : Γ(S, ⊤)ˣ →* Γ(G.left, ⊤)ˣ` to `Units.map G.hom.appTop.hom.toMonoidHom`. Establish `hinclv : ∀ u, (incl u).val = G.hom.appTop u.val` using `fun u => rfl`. Establish `hinj : Function.Injective incl`.

Introduce `u u' h`. Apply `Units.ext` to reduce the goal to its premises. Apply `hbij.1` to reduce the goal to its premises. Apply `FlatDescent.injective_appTop_of_epi q.left` to reduce the goal to its premises. Establish `h'` using `congrArg Units.val h`.

Rewrite `h'` using `[hinclv, hinclv, ← hq, appTop_comp_apply, appTop_comp_apply]`. Conclude with `h'`. Establish `hrange : ∀ m, f m ∈ incl.range`. Introduce `m`. Take `⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m` from `⟨Multiplicative.toAdd m, rfl⟩`.

Take `⟨v, hv, -⟩` from `(FlatDescent.existsUnique_units_appTop_eq_iff q.left hpb (f (Multiplicative.ofAdd χ))).2 (by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_map, Units.coe_map]`. Express the relevant statement in the definitionally equal form `(pullback.fst q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val = (pullback.snd q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val`. Rewrite using `[hfv]`.

Conclude with `key _)`. Set `e` to `RingEquiv.ofBijective B.hom.appTop.hom hbij`. Use `⟨Units.map e.symm.toMonoidHom v, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hv, hinclv]`. Express the relevant statement in the definitionally equal form `G.hom.appTop (e.symm v.val) = q.left.appTop v.val`.

Rewrite using `[← hq, appTop_comp_apply]`. Use `congr 1`. Conclude with `e.apply_symm_apply v.val`. Set `φ : Multiplicative X →* Γ(S, ⊤)ˣ` to `(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (f.codRestrict incl.range hrange)`. Establish `hφ : ∀ m, incl (φ m) = f m`.

Introduce `m`. Establish `h2` using `MonoidHom.ofInjective_apply hinj (x := (MonoidHom.ofInjective hinj).symm ⟨f m, hrange m⟩)`. Rewrite `h2` using `[MulEquiv.apply_symm_apply]`. Conclude with `h2.symm`. Use `⟨(splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ, ?_⟩` and prove the remaining obligations.

Apply `(splitTorusPointsEquiv S X G).injective` to reduce the goal to its premises. Use `MonoidHom.ext fun m => Units.ext ?_` and prove the remaining obligations. Take `⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m` from `⟨Multiplicative.toAdd m, rfl⟩`. Establish `h3` using `splitTorusPointsEquiv_val S X (𝟙_ (Over S)) ((splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ) χ`. Rewrite `h3` using `[MulEquiv.apply_symm_apply]`.

Rewrite using `[splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, toUnit_left, appTop_comp_apply, ← h3, ← hinclv, hφ, hfv]`.
-/
theorem eq_toUnit_comp_of_const_on_fibres : ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj B], IsAbelianScheme B → ∀ q : G ⟶ B, Flat q.left → Surjective q.left → QuasiCompact q.left → ∀ (X : Type) [AddCommGroup X] (d : G ⟶ splitTorus S X), (∀ (Z : Over S) (x y : Z ⟶ G), x ≫ q = y ≫ q → x ≫ d = y ≫ d) → ∃ a : 𝟙_ (Over S) ⟶ splitTorus S X, d = toUnit G ≫ a := by
  intro S G B _ hB q hfl hsu hqc X _ d hd
  have hE : EffectiveEpi q.left := inferInstance
  have hq : q.left ≫ B.hom = G.hom := Over.w q
  have hbij : Function.Bijective B.hom.appTop.hom := globalFns_holds S B hB

  have hpb := IsPullback.of_hasPullback q.left q.left
  let Z : Over S := Over.mk (pullback.fst q.left q.left ≫ G.hom)
  let x : Z ⟶ G := Over.homMk (pullback.fst q.left q.left) rfl
  let y : Z ⟶ G := Over.homMk (pullback.snd q.left q.left) (by
    change pullback.snd q.left q.left ≫ G.hom = pullback.fst q.left q.left ≫ G.hom
    rw [← hq, pullback.condition_assoc])
  have hxy : x ≫ q = y ≫ q := by
    ext1
    exact (pullback.condition (f := q.left) (g := q.left))
  have hdl : pullback.fst q.left q.left ≫ d.left = pullback.snd q.left q.left ≫ d.left :=
    congrArg CommaMorphism.left (hd Z x y hxy)
  have key : ∀ c : Γ((splitTorus S X).left, ⊤),
      (pullback.fst q.left q.left).appTop (d.left.appTop c) =
        (pullback.snd q.left q.left).appTop (d.left.appTop c) := fun c => by
    rw [← appTop_comp_apply, ← appTop_comp_apply, hdl]

  obtain ⟨f, hf⟩ : ∃ f, f = splitTorusPointsEquiv S X G d := ⟨_, rfl⟩
  have hfv : ∀ χ : X, (f (Multiplicative.ofAdd χ)).val = d.left.appTop (charUnit S X χ).val :=
    fun χ => hf ▸ splitTorusPointsEquiv_val S X G d χ
  let incl : Γ(S, ⊤)ˣ →* Γ(G.left, ⊤)ˣ := Units.map G.hom.appTop.hom.toMonoidHom
  have hinclv : ∀ u, (incl u).val = G.hom.appTop u.val := fun u => rfl
  have hinj : Function.Injective incl := by
    intro u u' h
    apply Units.ext
    apply hbij.1
    apply FlatDescent.injective_appTop_of_epi q.left
    have h' := congrArg Units.val h
    rw [hinclv, hinclv, ← hq, appTop_comp_apply, appTop_comp_apply] at h'
    exact h'
  have hrange : ∀ m, f m ∈ incl.range := by
    intro m
    obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
    obtain ⟨v, hv, -⟩ := (FlatDescent.existsUnique_units_appTop_eq_iff q.left hpb
      (f (Multiplicative.ofAdd χ))).2 (by
        apply Units.ext
        rw [Units.coe_map, Units.coe_map]
        change (pullback.fst q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val =
          (pullback.snd q.left q.left).appTop (f (Multiplicative.ofAdd χ)).val
        rw [hfv]
        exact key _)
    let e := RingEquiv.ofBijective B.hom.appTop.hom hbij
    refine ⟨Units.map e.symm.toMonoidHom v, Units.ext ?_⟩
    rw [← hv, hinclv]
    change G.hom.appTop (e.symm v.val) = q.left.appTop v.val
    rw [← hq, appTop_comp_apply]
    congr 1
    exact e.apply_symm_apply v.val
  let φ : Multiplicative X →* Γ(S, ⊤)ˣ :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (f.codRestrict incl.range hrange)
  have hφ : ∀ m, incl (φ m) = f m := by
    intro m
    have h2 := MonoidHom.ofInjective_apply hinj (x := (MonoidHom.ofInjective hinj).symm ⟨f m, hrange m⟩)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  refine ⟨(splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ, ?_⟩
  apply (splitTorusPointsEquiv S X G).injective
  refine MonoidHom.ext fun m => Units.ext ?_
  obtain ⟨χ, rfl⟩ : ∃ χ : X, Multiplicative.ofAdd χ = m := ⟨Multiplicative.toAdd m, rfl⟩
  have h3 := splitTorusPointsEquiv_val S X (𝟙_ (Over S))
    ((splitTorusPointsEquiv S X (𝟙_ (Over S))).symm φ) χ
  rw [MulEquiv.apply_symm_apply] at h3
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, toUnit_left,
    appTop_comp_apply, ← h3, ← hinclv, hφ, hfv]

end GlobalTheory
