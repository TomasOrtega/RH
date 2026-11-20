import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleIsoGenericExtendsNormalLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenExt

attribute [local instance] ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK

/- English proof (translation)
Introduce `R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂`. Use `haveI : IsNoetherianRing R' := hR.1`. Use `haveI : IsIntegrallyClosed R' := hR.2.2.1`. Establish `sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ` using `spMap_comp ρ (algebraMap R' (FractionRing R'))`. Establish `gpp` using `pull_grp p`.

Establish `g1` using `(pull_grp q₁).congr sc rfl`. Establish `g2` using `(pull_grp q₂).congr sc rfl`. Take `⟨κ, k₁, k₂⟩ : ∃ κ : E.P.A.left ⟶ D₃.P.A.left, κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧ κ ≫ D₃.P.A.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R'))` from `⟨gpp.1.lift _ _ (g1.1.w.trans (Category.assoc _ _ _).symm), gpp.1.lift_fst _ _ _, gpp.1.lift_snd _ _ _⟩`. Establish `gκ : IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ` using `IsGrpPullback.cancel gpp (g1.congr rfl k₁.symm) k₂`. Set `G₂` to `(Over.pullback (specOf ρ)).obj D₂.P.A`.

Establish `gb : IsGrpPullback G₂ D₂.P.A (spMap ρ) (pullback.fst D₂.P.A.hom (specOf ρ))` using `isGrpPullback_pullback _ _`. Take `⟨κ₂, l₁, l₂⟩ : ∃ κ₂ : E.P.A.left ⟶ G₂.left, κ₂ ≫ pullback.fst D₂.P.A.hom (specOf ρ) = GlobalTheory.PsiEvenPull.proj q₂ ∧ κ₂ ≫ G₂.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R'))` from `⟨gb.1.lift _ _ (g2.1.w.trans (Category.assoc _ _ _).symm), gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩`. Establish `gκ₂ : IsGrpPullback E.P.A G₂ (spMap (algebraMap R' (FractionRing R'))) κ₂` using `IsGrpPullback.cancel gb (g2.congr rfl l₁.symm) l₂`. Establish `hj : GlobalTheory.IsGenericPointHom (S` using `Sp R') (jK R') := .fractionField R' (FractionRing R')`. Establish `s₃ : IsSemiAbelian D₃.P.A` using `GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D₃.P.isAb`.

Establish `s₂ : IsSemiAbelian G₂` using `GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ D₂.P.isAb)`. Take `⟨F, ⟨hF, hκ⟩, -⟩` from `GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions (GlobalTheory.IsNormalScheme.pred _) hj s₃ s₂ gκ gκ₂`. Use `⟨F.hom.left ≫ pullback.fst D₂.P.A.hom (specOf ρ), κ, ?_, gκ, k₁, ?_⟩` and prove the remaining obligations. Conclude with `((isGrpPullback_of_iso F).comp gb).congr (Category.id_comp _) rfl`. Rewrite using `[← Category.assoc, hκ, l₁]`.
-/
theorem grp : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E), ∃ (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ ∧ IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ ∧ κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧ κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  haveI : IsNoetherianRing R' := hR.1
  haveI : IsIntegrallyClosed R' := hR.2.2.1
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have g1 := (pull_grp q₁).congr sc rfl
  have g2 := (pull_grp q₂).congr sc rfl

  obtain ⟨κ, k₁, k₂⟩ : ∃ κ : E.P.A.left ⟶ D₃.P.A.left, κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧
      κ ≫ D₃.P.A.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gpp.1.lift _ _ (g1.1.w.trans (Category.assoc _ _ _).symm), gpp.1.lift_fst _ _ _, gpp.1.lift_snd _ _ _⟩
  have gκ : IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ :=
    IsGrpPullback.cancel gpp (g1.congr rfl k₁.symm) k₂

  let G₂ := (Over.pullback (specOf ρ)).obj D₂.P.A
  have gb : IsGrpPullback G₂ D₂.P.A (spMap ρ) (pullback.fst D₂.P.A.hom (specOf ρ)) := isGrpPullback_pullback _ _
  obtain ⟨κ₂, l₁, l₂⟩ : ∃ κ₂ : E.P.A.left ⟶ G₂.left, κ₂ ≫ pullback.fst D₂.P.A.hom (specOf ρ) = GlobalTheory.PsiEvenPull.proj q₂ ∧
      κ₂ ≫ G₂.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gb.1.lift _ _ (g2.1.w.trans (Category.assoc _ _ _).symm), gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gκ₂ : IsGrpPullback E.P.A G₂ (spMap (algebraMap R' (FractionRing R'))) κ₂ :=
    IsGrpPullback.cancel gb (g2.congr rfl l₁.symm) l₂
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R') (jK R') := .fractionField R' (FractionRing R')
  have s₃ : IsSemiAbelian D₃.P.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D₃.P.isAb
  have s₂ : IsSemiAbelian G₂ :=
    GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ D₂.P.isAb)
  obtain ⟨F, ⟨hF, hκ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj s₃ s₂ gκ gκ₂
  refine ⟨F.hom.left ≫ pullback.fst D₂.P.A.hom (specOf ρ), κ, ?_, gκ, k₁, ?_⟩
  · exact ((isGrpPullback_of_iso F).comp gb).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, hκ, l₁]

/- English proof (translation)
Introduce `R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂`. Take `⟨w₀, hw₀⟩` from `GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂`. Take `⟨w, hw, hr⟩` from `GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification R R' ρ D₂ D₃ Φ gp w₀ hw₀`. Conclude with `⟨w, hw, hr, GlobalTheory.T.rigidified_identifications_generic_fibre_agree R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ w hw hr⟩`.
-/
theorem bundle : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w, hw, hr⟩ := GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification R R' ρ D₂ D₃ Φ gp w₀ hw₀
  exact ⟨w, hw, hr, GlobalTheory.T.rigidified_identifications_generic_fibre_agree R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ w hw hr⟩

/- English proof (translation)
Introduce `R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ x`. Use `set y := q₁.xe.symm (p.xe x) with hy`. Establish `hy' : q₁.xe y = p.xe x` using `q₁.xe.apply_symm_apply _`. Establish `sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = jK R' ≫ spMap ρ` using `spMap_comp ρ (algebraMap R' (FractionRing R'))`. Establish `gpp` using `pull_grp p`.

Establish `b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _` using `by simpa using Over.w (E.c y)`. Establish `b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _` using `by simpa using Over.w (D₃.c x)`. Establish `cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ = spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left`. Rewrite using `[← hy']`. Conclude with `q₁.c_pr y`.

Establish `cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left` using `p.c_pr x`. Establish `hx : (E.c y).left ≫ κ = jK R' ≫ (D₃.c x).left`. Apply `gpp.1.hom_ext` to reduce the goal to its premises. Use `show ((E.c y).left ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p`. Rewrite using `[Category.assoc, h₁, cq, Category.assoc, cp, sc, Category.assoc]`.

Rewrite using `[Category.assoc, gκ.1.w, ← Category.assoc, b1, Category.id_comp, Category.assoc, b3]`. Conclude with `(Category.comp_id _).symm`. Establish `c2 : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₂ = spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₂.c (q₂.xe y)).left` using `q₂.c_pr y`. Establish `hsep` using `(GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian D₂.P.A (GlobalTheory.isSemiAbelian_of_isAbelianScheme D₂.P.A D₂.P.isAb)).2`. Establish `b2 : (D₂.c (q₂.xe y)).left ≫ D₂.P.A.hom = 𝟙 _` using `by simpa using Over.w (D₂.c (q₂.xe y))`.

Use `haveI := hsep`. Use `ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R')) D₂.P.A.hom ?_ (jK R') ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, gp.1.w, ← Category.assoc, b3, Category.assoc, b2]`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`. Rewrite using `[← Category.assoc, ← hx, Category.assoc, h₂, c2, sc, Category.assoc]`.
-/
theorem cpt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ x : D₃.X, (D₃.c x).left ≫ Φ = spMap ρ ≫ (D₂.c (q₂.xe (q₁.xe.symm (p.xe x)))).left := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ x
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = jK R' ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have hx : (E.c y).left ≫ κ = jK R' ≫ (D₃.c x).left := by
    apply gpp.1.hom_ext
    · show ((E.c y).left ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
      rw [Category.assoc, h₁, cq, Category.assoc, cp, sc, Category.assoc]
    · rw [Category.assoc, gκ.1.w, ← Category.assoc, b1, Category.id_comp, Category.assoc, b3]
      exact (Category.comp_id _).symm
  have c2 : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₂ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₂.c (q₂.xe y)).left := q₂.c_pr y
  have hsep := (GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian D₂.P.A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme D₂.P.A D₂.P.isAb)).2
  have b2 : (D₂.c (q₂.xe y)).left ≫ D₂.P.A.hom = 𝟙 _ := by simpa using Over.w (D₂.c (q₂.xe y))
  haveI := hsep
  refine ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R')) D₂.P.A.hom ?_ (jK R') ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, b3, Category.assoc, b2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [← Category.assoc, ← hx, Category.assoc, h₂, c2, sc, Category.assoc]

end GlobalTheory.Mum.GenExt

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂`. Establish `hα : Function.Injective (algebraMap R' (FractionRing R'))` using `IsFractionRing.injective R' _`. Take `⟨Φ, κ, gp, gκ, h₁, h₂⟩` from `GenExt.grp R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂`. Take `⟨w, hw, hr, hT⟩` from `GenExt.bundle R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂`. Establish `hc` using `GenExt.cpt R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂`.

Take `⟨s, hs⟩` from `GlobalTheory.PullDegComp.exists_generic_lift (show Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) from hα.comp hρ) q₂`. Set `lf : FractionRing (FractionRing R') →+* FractionRing R'` to `IsFractionRing.lift (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id`. Set `r' : (TK R').left ⟶ (TK (FractionRing R')).left` to `spMap lf`. Establish `hrj : r' ≫ jK (FractionRing R') = 𝟙 _` using `by show spMap lf ≫ spMap (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = 𝟙 _`. Rewrite using `[← spMap_comp]`.

Establish `: lf.comp (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = RingHom.id _` using `RingHom.ext fun a => IsFractionRing.lift_algebraMap (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id a`. Rewrite using `[this]`. Conclude with `Spec.map_id _`. Establish `hr2 : r' ≫ jK (FractionRing R') ≫ spMap ((algebraMap R' (FractionRing R')).comp ρ) = GlobalTheory.ArcPull.genMap hρ ≫ jK R`. Use `(Category.assoc _ _ _).symm.trans ?_` and prove the remaining obligations.

Rewrite using `[hrj, Category.id_comp]`. Conclude with `(spMap_comp ρ (algebraMap R' (FractionRing R'))).trans ((Category.id_comp _).symm.trans (GlobalTheory.ArcPull.fracMap_sq hρ))`. Use `⟨(GlobalTheory.DvrDeg.exists_isPullDeg_of_val hρ D₂ D₃ q₂.psiW s hs gp w hw hr (p.xe.trans (q₁.xe.symm.trans q₂.xe)) hc (fun x z J J' hJ hJ' => ?_)).choose⟩` and prove the remaining obligations. Use `set y := q₁.xe.symm (p.xe x) with hy`. Establish `hy' : q₁.xe y = p.xe x` using `q₁.xe.apply_symm_apply _`.

Use `set e : (TK R').left ⟶ E.P.A.left := r' ≫ E.xK y with he`. Establish `gpp` using `pull_grp p`. Establish `b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _` using `by simpa using Over.w (E.c y)`. Establish `b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _` using `by simpa using Over.w (D₃.c x)`. Establish `cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ = spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left`.

Rewrite using `[← hy']`. Conclude with `q₁.c_pr y`. Establish `cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left` using `p.c_pr x`. Establish `a1 : (e ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p`. Rewrite using `[Category.assoc, h₁]`.

Use `show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ GlobalTheory.PsiEvenPull.proj q₁ = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p`. Rewrite using `[Category.assoc, Category.assoc, cq, Category.assoc, cp, ← Category.assoc (jK (FractionRing R')), ← Category.assoc r', hr2, ← Category.assoc (jK R'), ← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]`. Establish `a2 : (e ≫ κ) ≫ D₃.P.A.hom = D₃.xK x ≫ D₃.P.A.hom`. Rewrite using `[Category.assoc, gκ.1.w]`. Use `show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) = (jK R' ≫ (D₃.c x).left) ≫ D₃.P.A.hom`.

Simplify using `only [Category.assoc, reassoc_of% b1, b3, Category.id_comp, Category.comp_id]`. Rewrite using `[← Category.assoc, hrj, Category.id_comp]`. Both sides reduce to the same expression. Establish `hx : e ≫ κ = D₃.xK x` using `gpp.1.hom_ext a1 a2`. Take `⟨JE, hJE⟩` from `GlobalTheory.DegPull.exists_good' E.P.isLB z`.

Take `⟨J₁, hJ₁⟩` from `GlobalTheory.DegPull.exists_good' D₁.P.isLB z`. Establish `v₂` using `GlobalTheory.ArcPull.psi_val q₂ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ hJE y`. Establish `v₁` using `GlobalTheory.ArcPull.psi_val q₁ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ₁ hJE y`. Establish `v₃` using `GlobalTheory.ArcPull.psi_val p (GlobalTheory.ArcPull.genMap hρ) (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' x`. Rewrite `v₁` using `[hy']`.

Rewrite `v₃` using `[v₁, Category.id_comp]`. Establish `ex₂ : e ≫ GlobalTheory.PsiEvenPull.proj q₂ = D₃.xK x ≫ Φ` using `by rw [← h₂, ← Category.assoc, hx]`. Establish `ex₁ : e ≫ GlobalTheory.PsiEvenPull.proj q₁ = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p` using `by rw [← h₁, ← Category.assoc, hx]`. Establish `t` using `hT _ e z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) (JE e) (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (by rw [← Scheme.Hom.comp_apply, ex₂]; exact hJ _) (by rw [← Scheme.Hom.comp_apply, hx]; exact hJ' _) (hJE e) (by rw [← Scheme.Hom.comp_apply, ex₁]; exact hJ₁ _)`. Simplify using `only [hx] at t`.

Establish `o₂ : GlobalTheory.ArcPull.om q₂.w z J JE e = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e)`. Unfold `GlobalTheory.ArcPull.om`. Rewrite using `[ex₂]`. Establish `o₁ : GlobalTheory.ArcPull.om q₁.w z J₁ JE e = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e)`. Unfold `GlobalTheory.ArcPull.om`.

Rewrite using `[ex₁]`. Establish `oo : GlobalTheory.ArcPull.om w z J J' (D₃.xK x) = gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x))` using `rfl`. Establish `op : GlobalTheory.ArcPull.om p.w z J₁ J' (D₃.xK x) = gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x))` using `rfl`. Express the relevant statement in the definitionally equal form `val (D₂.psi (q₂.xe y)) _ z J = _`. Rewrite using `[v₂, oo, o₂]`.

Rewrite `v₃` using `[o₁, op]`. Establish `v₄ : val (E.psi y) r' z JE = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) * ((gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)))⁻¹ * val (D₃.psi x) (𝟙 _) z J')`. Rewrite using `[← v₃, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]`. Rewrite using `[v₄]`. Establish `t' : gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) * (gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e))⁻¹ * gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x))`.

Rewrite using `[← t, inv_mul_cancel_right]`. Rewrite using `[t']`. Simplify using `only [mul_inv_rev, inv_inv]`. The two sides agree by associativity and commutativity.
-/
theorem isPullDeg_of_generic : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')), IsPullDeg ρ D₁ D₃ → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E → Nonempty (IsPullDeg ρ D₂ D₃) := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  have hα : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' _
  obtain ⟨Φ, κ, gp, gκ, h₁, h₂⟩ := GenExt.grp R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  obtain ⟨w, hw, hr, hT⟩ := GenExt.bundle R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  have hc := GenExt.cpt R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift (show Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) from hα.comp hρ) q₂

  let lf : FractionRing (FractionRing R') →+* FractionRing R' :=
    IsFractionRing.lift (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id
  let r' : (TK R').left ⟶ (TK (FractionRing R')).left := spMap lf
  have hrj : r' ≫ jK (FractionRing R') = 𝟙 _ := by
    show spMap lf ≫ spMap (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = 𝟙 _
    rw [← spMap_comp]
    have : lf.comp (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = RingHom.id _ :=
      RingHom.ext fun a => IsFractionRing.lift_algebraMap (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id a
    rw [this]; exact Spec.map_id _
  have hr2 : r' ≫ jK (FractionRing R') ≫ spMap ((algebraMap R' (FractionRing R')).comp ρ) =
      GlobalTheory.ArcPull.genMap hρ ≫ jK R := by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hrj, Category.id_comp]
    exact (spMap_comp ρ (algebraMap R' (FractionRing R'))).trans ((Category.id_comp _).symm.trans (GlobalTheory.ArcPull.fracMap_sq hρ))
  refine ⟨(GlobalTheory.DvrDeg.exists_isPullDeg_of_val hρ D₂ D₃ q₂.psiW s hs gp w hw hr
    (p.xe.trans (q₁.xe.symm.trans q₂.xe)) hc (fun x z J J' hJ hJ' => ?_)).choose⟩
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  set e : (TK R').left ⟶ E.P.A.left := r' ≫ E.xK y with he
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have a1 : (e ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by
    rw [Category.assoc, h₁]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
    rw [Category.assoc, Category.assoc, cq, Category.assoc, cp, ← Category.assoc (jK (FractionRing R')),
      ← Category.assoc r', hr2, ← Category.assoc (jK R'), ← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  have a2 : (e ≫ κ) ≫ D₃.P.A.hom = D₃.xK x ≫ D₃.P.A.hom := by
    rw [Category.assoc, gκ.1.w]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) =
      (jK R' ≫ (D₃.c x).left) ≫ D₃.P.A.hom
    simp only [Category.assoc, reassoc_of% b1, b3, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hrj, Category.id_comp]; rfl
  have hx : e ≫ κ = D₃.xK x := gpp.1.hom_ext a1 a2
  obtain ⟨JE, hJE⟩ := GlobalTheory.DegPull.exists_good' E.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.DegPull.exists_good' D₁.P.isLB z
  have v₂ := GlobalTheory.ArcPull.psi_val q₂ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ hJE y
  have v₁ := GlobalTheory.ArcPull.psi_val q₁ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ₁ hJE y
  have v₃ := GlobalTheory.ArcPull.psi_val p (GlobalTheory.ArcPull.genMap hρ) (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' x
  rw [hy'] at v₁
  rw [v₁, Category.id_comp] at v₃
  have ex₂ : e ≫ GlobalTheory.PsiEvenPull.proj q₂ = D₃.xK x ≫ Φ := by rw [← h₂, ← Category.assoc, hx]
  have ex₁ : e ≫ GlobalTheory.PsiEvenPull.proj q₁ = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by rw [← h₁, ← Category.assoc, hx]
  have t := hT _ e z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) (JE e) (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p))
    (by rw [← Scheme.Hom.comp_apply, ex₂]; exact hJ _) (by rw [← Scheme.Hom.comp_apply, hx]; exact hJ' _) (hJE e)
    (by rw [← Scheme.Hom.comp_apply, ex₁]; exact hJ₁ _)
  simp only [hx] at t
  have o₂ : GlobalTheory.ArcPull.om q₂.w z J JE e = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₂]
  have o₁ : GlobalTheory.ArcPull.om q₁.w z J₁ JE e = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₁]
  have oo : GlobalTheory.ArcPull.om w z J J' (D₃.xK x) = gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) := rfl
  have op : GlobalTheory.ArcPull.om p.w z J₁ J' (D₃.xK x) =
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := rfl
  change val (D₂.psi (q₂.xe y)) _ z J = _
  rw [v₂, oo, o₂]
  rw [o₁, op] at v₃
  have v₄ : val (E.psi y) r' z JE = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) *
      ((gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)))⁻¹ *
        val (D₃.psi x) (𝟙 _) z J') := by
    rw [← v₃, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [v₄]
  have t' : gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) =
      gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) * (gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e))⁻¹ *
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := by
    rw [← t, inv_mul_cancel_right]
  rw [t']
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.Mum
