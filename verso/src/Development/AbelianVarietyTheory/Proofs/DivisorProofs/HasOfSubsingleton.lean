import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSecTieFModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR D hX`. Use `haveI : IsNoetherianRing R := hR.1`. Set `A : PolAV (Spec (CommRingCat.of (FractionRing R)))` to `GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK R)`. Set `eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A` to `Iso.refl _`. Establish `hA : IsMonHom eA.hom`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Category.comp_id _`. Use `show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ`. Rewrite using `[Category.comp_id, id_tensorHom_id, Category.id_comp]`. Both sides reduce to the same expression.

Establish `hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen`. Take `⟨w, hw⟩` from `GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK R)))`. Conclude with `⟨GlobalTheory.PtTie.isoFromPullId w, GlobalTheory.PtTie.isoFromPullId_isGen hw⟩`. Establish `hI : maximalIdeal R ≤ Ideal.jacobson ⊥` using `(IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge`. Conclude with `⟨D.toPre.P.A, inferInstance, inferInstance, A, GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb, ⟨⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ => GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds hI k⟩⟩⟩`.
-/
theorem has_of_subsingleton : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ D : DegData R (maximalIdeal R), Subsingleton D.toPre.X → Has D := by
  intro R _ _ _ hR D hX
  haveI : IsNoetherianRing R := hR.1
  let A : PolAV (Spec (CommRingCat.of (FractionRing R))) := GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK R)
  let eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A := Iso.refl _
  have hA : IsMonHom eA.hom := by
    refine ⟨?_, ?_⟩
    · exact Category.comp_id _
    · show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      rfl
  have hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen := by
    obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK R)))
    exact ⟨GlobalTheory.PtTie.isoFromPullId w, GlobalTheory.PtTie.isoFromPullId_isGen hw⟩
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact ⟨D.toPre.P.A, inferInstance, inferInstance, A, GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb,
    ⟨⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ =>
      GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds hI k⟩⟩⟩

end GlobalTheory.Mum
