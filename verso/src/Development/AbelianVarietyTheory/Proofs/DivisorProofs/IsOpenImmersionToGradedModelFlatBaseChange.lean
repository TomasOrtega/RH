import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiAffineCartierSectionGeneratingLocusAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelBaseChangeStandardOpenAppInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.OpenImmersionDescent

/- English proof (translation)
Establish `e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv`. Rewrite using `[← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem openImm_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine Y] [X.IsQuasiAffine] (g : X ⟶ Y) [IsIso g.appTop] :
    IsOpenImmersion g := by
  have e : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  rw [e]; infer_instance

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hb`.
-/
theorem bij_congr {X Y : Scheme.{0}} (f : X ⟶ Y) (V W : Y.Opens) (h : V = W) (hb : Function.Bijective (f.app W)) :
    Function.Bijective (f.app V) := by subst h; exact hb

end GlobalTheory.Desc.OpenImmersionDescent

open GlobalTheory.Desc.OpenImmersionDescent in

/- English proof (translation)
Introduce `R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_` and prove the remaining obligations. Take `⟨k, hk, b, hb, hz⟩` from `hP.cover (pullback.fst p (spMap ρ) z)`. Use `⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)`. Establish `hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)` using `(hP.affine k hk b hb).preimage _`. Use `haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA`. Establish `hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b)`. Use extensionality with `y`.

Express the relevant statement in the definitionally equal form `pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.lift_fst]`. Conclude with `hloc k hk b hb y`. Use `haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine := GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre`. Use `haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by`.

Rewrite using `[morphismRestrict_appTop]`. Establish `h1` using `bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _) ⟨GlobalTheory.T.proj_model_baseChange_standard_open_app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb, GlobalTheory.T.proj_model_baseChange_standard_open_app_surje …`. Establish `h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤))` using `(ConcreteCategory.isIso_iff_bijective _).2 h1`. Conclude with `@IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)`. Conclude with `openImm_of_isIso_appTop _`.
-/
theorem GlobalTheory.Desc.openIn_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ → PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → OpenIn m q p (spMap ρ) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hP R₁ _ _ ρ hρ hc₀ Y _ _ _ q θ D₁ hθ hLD hamp hSec m hm hPFF hloc
  refine ⟨hm, ?_⟩
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsOpenImmersion) fun z => ?_
  obtain ⟨k, hk, b, hb, hz⟩ := hP.cover (pullback.fst p (spMap ρ) z)
  refine ⟨(pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b, hz, ?_⟩
  haveI : IsAffineHom (pullback.fst p (spMap ρ)) := by first | infer_instance | exact MorphismProperty.pullback_fst (P := @IsAffineHom) p (spMap ρ) inferInstance | exact (isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (spMap ρ)).flip inferInstance)
  have hA : IsAffineOpen ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) := (hP.affine k hk b hb).preimage _
  haveI : IsAffine ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b).toScheme := hA
  have hpre : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b) : Set Y) = locus D₁ k (θ b) := by
    ext y
    change pullback.fst p (spMap ρ) (pullback.lift m q hm y) ∈ Dp k b ↔ _
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hloc k hk b hb y
  haveI : ((pullback.lift m q hm) ⁻¹ᵁ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).toScheme.IsQuasiAffine :=
    GlobalTheory.T.isQuasiAffine_cartierSectionGeneratingLocus_ample Y D₁ hamp k hk (θ b) (by rw [hSec]; exact subset_spanBy _ _ ⟨b, hb, rfl⟩) _ hpre
  haveI : IsIso (pullback.lift m q hm ∣_ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := bij_congr (pullback.lift m q hm) _ _ (Scheme.Opens.ι_image_top _)
      ⟨GlobalTheory.T.proj_model_baseChange_standard_open_app_injective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb,
       GlobalTheory.T.proj_model_baseChange_standard_open_app_surjective R F c₀ N hN P p ψ Dp hP R₁ ρ hρ hc₀ Y q θ D₁ hθ hLD hamp hSec m hPFF hloc hm k hk b hb⟩
    have h2 : IsIso (Scheme.Hom.app (pullback.lift m q hm) ((pullback.fst p (spMap ρ) ⁻¹ᵁ Dp k b).ι ''ᵁ ⊤)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 h1
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact openImm_of_isIso_appTop _
