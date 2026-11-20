import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `R _ _ _ _ X S j A _ G _ e hG hA G₁ _ hG₁ ξ y hyj B _ a b ha hb`. Establish `hBG : IsGrpPullback B G (jK R ≫ ξ) (b ≫ e)` using `(hb.comp hA).congr hyj rfl`. Establish `hG₂ : IsGrpPullback ((Over.pullback ξ).obj G) G ξ (pullback.fst G.hom ξ)` using `isGrpPullback_pullback G ξ`. Establish `hsG₂ : IsSemiAbelian ((Over.pullback ξ).obj G)` using `IsSemiAbelian.pullback ξ G hG`. Establish `hw : (b ≫ e) ≫ G.hom = (B.hom ≫ jK R) ≫ ξ` using `by rw [hBG.1.w, Category.assoc]`.

Set `i₂ : B.left ⟶ ((Over.pullback ξ).obj G).left` to `pullback.lift (b ≫ e) (B.hom ≫ jK R) hw`. Establish `hi₂ : i₂ ≫ pullback.fst G.hom ξ = b ≫ e` using `pullback.lift_fst _ _ _`. Establish `hBG₂ : IsGrpPullback B ((Over.pullback ξ).obj G) (jK R) i₂` using `hG₂.cancel (hBG.congr rfl hi₂.symm) (pullback.lift_snd _ _ _)`. Establish `hj : GlobalTheory.IsGenericPointHom (S` using `Sp R) (ReciprocityTheory.ChartRestriction.G.Out.jK R) := .fractionField R (FractionRing R)`. Take `⟨_, _⟩` from `hj.quasiCompact_and_dominant`.

Take `⟨_, -⟩` from `GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁`. Take `⟨-, _⟩` from `GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hsG₂`. Take `⟨E, ⟨hE, hEa⟩, -⟩` from `GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions (GlobalTheory.IsNormalScheme.pred _) hj hG₁ hsG₂ ha hBG₂`. Use `haveI := hE`. Use `⟨E.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E).comp hG₂).congr (Category.id_comp _) rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, hEa, hi₂]`.
-/
theorem GlobalTheory.SemiAbDesc.exists_grpPullback_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  intro R _ _ _ _ X S j A _ G _ e hG hA G₁ _ hG₁ ξ y hyj B _ a b ha hb
  have hBG : IsGrpPullback B G (jK R ≫ ξ) (b ≫ e) := (hb.comp hA).congr hyj rfl
  have hG₂ : IsGrpPullback ((Over.pullback ξ).obj G) G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hsG₂ : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback ξ G hG
  have hw : (b ≫ e) ≫ G.hom = (B.hom ≫ jK R) ≫ ξ := by rw [hBG.1.w, Category.assoc]
  let i₂ : B.left ⟶ ((Over.pullback ξ).obj G).left := pullback.lift (b ≫ e) (B.hom ≫ jK R) hw
  have hi₂ : i₂ ≫ pullback.fst G.hom ξ = b ≫ e := pullback.lift_fst _ _ _
  have hBG₂ : IsGrpPullback B ((Over.pullback ξ).obj G) (jK R) i₂ :=
    hG₂.cancel (hBG.congr rfl hi₂.symm) (pullback.lift_snd _ _ _)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (ReciprocityTheory.ChartRestriction.G.Out.jK R) := .fractionField R (FractionRing R)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hsG₂
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj hG₁ hsG₂ ha hBG₂
  haveI := hE
  refine ⟨E.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E).comp hG₂).congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, hEa, hi₂]
