import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy`. Establish `iφ : IsClosedImmersion φ` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)`. Establish `iφ₀ : IsClosedImmersion φ₀` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)`. Take `⟨f, c, hc, rfl, hred⟩` from `hy`. Take `⟨c₀, hc₀, hcl⟩` from `((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred`.

Rewrite `hcl` using `[map_zero, CatCoh.H1.mk_eq_zero]`. Take `⟨g₀, hg₀⟩` from `hcl`. Establish `hS` using `GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF`. Use `choose g hg using fun U => (hS U).2.2.1 (g₀ U)`. Establish `key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0`.

Introduce `U V a`. Rewrite using `[← (hS V).2.2.2]`. Establish `hn` using `(preCoef h₀.w).naturality a (g U)`. Establish `e` using `congrFun (congrFun (congrFun hg₀ U) V) a`. Express the relevant statement in the definitionally equal form `preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn`.

Rewrite `e` using `[amitsur_d0_apply, hc₀]`. Rewrite using `[amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]`. Expand and normalize the polynomial expressions, which then agree. Use `CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_smul]`.

Use function extensionality and compare the values at `U V a`. Use `key U V a` as an intermediate fact. Simplify using `only [Pi.smul_apply]`. Rewrite `this` using `[smul_sub, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem tMul_zero_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.AbCoh
