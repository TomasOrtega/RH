import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `hd : Dense ({genericPoint X} : Set X)`. Rewrite using `[dense_iff_closure_eq]`. Conclude with `(genericPoint_spec X).def`. Conclude with `hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)`.
-/
theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

/- English proof (translation)
Establish `h1 : gp X q ⤳ genericPoint X`. Establish `: gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X))` using `⟨q, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Conclude with `this`. Conclude with `(h1.antisymm (genericPoint_specializes _)).eq`.
-/
theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

/- English proof (translation)
Take `⟨l, h₁, h₂⟩` from `h`. Establish `e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme`. Rewrite using `[← cancel_mono V.ι, Category.assoc, h₁]`. Conclude with `GlobalTheory.specMap_functionFieldMap V.ι`. Establish `e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X = Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X`.

Use `Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm` and prove the remaining obligations. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`. Use `erw [← h₂]`. Rewrite using `[← Category.assoc, e1]`. Use `haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))`.
-/
theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

/- English proof (translation)
Introduce `X Y _ _ V φ θ D D₁ hF hP`. Take `⟨l, h₁, h₂⟩` from `hF`. Take `⟨q⟩ : Nonempty (Sp Y.functionField)` from `inferInstance`. Use `haveI : Nonempty V := ⟨l q⟩`. Use `haveI : IsIntegral V.toScheme := inferInstance`.

Use `haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by`. Rewrite using `[← Scheme.Hom.comp_apply, h₁, gp_apply])`. Use `haveI : IsDominant φ := isDominant_of_gen φ (l q) (by`. Rewrite using `[← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])`. Establish `key` using `ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩`.

Establish `hE : pullback V.ι D₁ = pullback φ D` using `CartierDiv.ext_of_isEqn fun v => by`. Take `⟨g, hg⟩` from `D.exists_isEqn (φ v)`. Use `⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩` and prove the remaining obligations. Use `isEqn_pullback V.ι D₁ (hP v g hg)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `ext`. Simplify using `only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Conclude with `(congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm`. Conclude with `(presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)`.
-/
theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
