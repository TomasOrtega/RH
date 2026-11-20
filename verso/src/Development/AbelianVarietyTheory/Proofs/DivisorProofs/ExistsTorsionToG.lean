import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsPullF
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ToricTorsionSecUnif

section FinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

/- English proof (translation)
Take `⟨_, -, -, hc⟩` from `hR`. Establish `hL` using `abelianSchemeLaws_all.1`. Take `⟨Gt, _, _, hH⟩` from `exists_isGt hL.globalFns (splitExt D.toPre)`. Take `⟨Φ, hΦ⟩` from `exists_points hL.globalFns hH`. Establish `hΦ : Represents Φ` using `hΦ`.

Establish `hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom`. Take `⟨h₁, h₂, -⟩` from `hL.mulN _ D.toPre.P k hk`. Establish `h₁' : IsFinite (𝟙 D.toPre.P.A ^ k).left` using `h₁`. Establish `h₂' : Flat (𝟙 D.toPre.P.A ^ k).left` using `h₂`. Rewrite `h₁'`, `h₂'` using `[← MulEtaleDvr.mulN_eq_pow]`.

Establish `Q` using `MulEtaleDvr.isPullback_torsion D.toPre.P.A k`. Conclude with `isFinite_flat_torsion_of_isGt _ (splitExt D.toPre) Gt hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')`. Take `⟨hf, hl⟩` from `hfin`. Take `⟨J, hJ⟩` from `exists_mulEquiv U.toUnifPre hL.globalFns hΦ`. Establish `hN` using `isAdicColimit_of_isFinite hc (torsion Gt k)`.

Use `⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl, (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_, (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(Φ T).surjective g`. Establish `hx` using `(tors_iff hΦ k x).1 hg`. Use `⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩` and prove the remaining obligations. Rewrite using `[torsionLift_ι]`.

Conclude with `(isPull_iff_comp hΦ _ _ _).1 hh`. Rewrite using `[← map_pow, torsionι_pow, map_one]`.
-/
theorem exists_torsion_toG (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.toPre.P k hk
    have h₁' : IsFinite (𝟙 D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

/- English proof (translation)
Establish `hL` using `firstFiveLaws`. Use `hfin` as an intermediate fact. Take `⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩` from `exists_normal_point R hR F N x hx`. Establish `hφ : Function.Injective φ` using `fun a b e => IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))`. Take `⟨D', hD, A', U', hU⟩` from `UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange hL.2.2.2.2.psiOnExists hR hR' φ hφ hI hG U`.

Establish `hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ` using `hξ.trans (Category.id_comp _).symm`. Take `⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T'` from `𝟙_ _) ξ g₀ gp := ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr (T' := 𝟙_ _) ξ hh g₀`. Set `x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj G` to `Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh)) (pullback.lift_snd _ _ _)`. Establish `e₁ : x₁.left ≫ pullback.fst G.hom (specOf φ) = ξ ≫ x₀.left` using `pullback.lift_fst _ _ _`. Establish `e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) = ξ ≫ x₀.left` using `(congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁`.

Establish `gG` using `isGrpPullback_pullback G (spMap φ)`. Establish `hk₁ : x₁ ^ k = 1` using `ConstGrp.push_injective gG _ (by`. Set `ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N` to `Over.homMk ξ hh`. Establish `e : pushHom gG _ x₁ = ρ ≫ x₀` using `Over.OverMorphism.ext e₁`. Rewrite using `[map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])`.

Establish `hp` using `isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)`. Take `⟨g', hg'⟩` from `FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp`. Set `y : TFK (R` to `R) F ⟶ (Over.pullback (jK R)).obj G := Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F) (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)`. Establish `hy : (y ≫ U.gen.hom).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = ((jFK (R` using `R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by`. Rewrite using `[← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.

Conclude with `pullback.lift_fst _ _ _`. Use `⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ D A G U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁ (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩` and prove the remaining obligations. Set `xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj G))` to `Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)) (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))`. Establish `hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`. Establish `c` using `hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)`.

Conclude with `⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩`. Rewrite using `[hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]`. Conclude with `Category.assoc _ _ _`.
-/
theorem generic (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G)
    (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp R)) (g₀ : GtPt D.toPre N)
    (x₀ : N ⟶ G) (hfin : IsFinite N.hom) (htors : x₀ ^ k = 1) (hform : FormalEq U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left) (hx : OverGen F N x)
    (q : QkPt D.toPre F k) (hq : q.y = 0) (hg : GtPt.IsPullF F x g₀ q.g) :
    ∃ y : TFK (R := R) F ⟶ A.A, y.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x ≫ x₀.left ∧
      QkToAkU U.toUnifPre F k q y := by
  have hL := firstFiveLaws
  have := hfin
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI hG U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U.gen.hom).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ D A G U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end FinitePart

section TorusPoint

/- English proof (translation)
Establish `ha' : ∀ x ∈ maximalIdeal R, (f.comp a) x = 0` using `fun x hx => by`. Rewrite using `[RingHom.comp_apply, ha x hx, map_zero]`. Establish `hρ` using `GlobalTheory.TorusPart.map_pow_one_eq_zero ha`. Establish `hρ'` using `GlobalTheory.TorusPart.map_pow_one_eq_zero ha'`. Establish `eR : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero ha) hm₀).left ≫ m₀ = (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X ≫ (U.gt 0).i.left) ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0)`.

Rewrite using `[Over.comp_left, Category.assoc]`. Establish `k` using `GlobalTheory.TorusPart.gtTorus_left (U.gt 0) hρ hm₀`. Conclude with `(congrArg (z.left ≫ ·) k).trans (by simp only [Category.assoc])`. Establish `hN : (h.left ≫ x₀.left) ≫ G.hom = GlobalTheory.TorusPart.thickPt 0 hρ' ≫ thick R (maximalIdeal R) 0`. Rewrite using `[GlobalTheory.TorusPart.thickPt_thick, Category.assoc, Over.w x₀, Over.w h]`.

Both sides reduce to the same expression. Set `y₁ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 G).left` to `pullback.lift (h.left ≫ x₀.left) (GlobalTheory.TorusPart.thickPt 0 hρ') hN`. Set `y₂ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 G).left` to `z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X ≫ (U.gt 0).i.left`. Establish `e₁ : h.left ≫ x₀.left = y₁ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0)` using `(pullback.lift_fst _ _ _).symm`. Establish `hP` using `(GlobalTheory.TorsionFormCompare.formalEq_iff U.toUnifPre x₀ g₀).1 hform`.

Establish `hc` using `hP 0 (Sp A') h.left y₁ e₁.symm`. Take `⟨hb, hv⟩` from `(GlobalTheory.FormalPoint.hasCoords_iff _ 0 g₀ h.left y₁).1 hc`. It suffices to establish `hy : y₁ = y₂ by rw [eR, e₁, hy]`. Use `GlobalTheory.TorusCoord.ext_of_val (U.gt 0) y₁ y₂ ?_ ?_` and prove the remaining obligations. Rewrite using `[hb, ← hpull.1, (hg 0).1, GlobalTheory.TorusCoord.pG_left]`.

Establish `hk : (U.gt 0).i.left ≫ (U.gt 0).q.left = (splitTorus _ D.toPre.X).hom ≫ eSec (thickObj R (maximalIdeal R) 0 D.toPre.P.A)`. Use `congrArg Over.Hom.left (U.gt 0).isKernel.w` as an intermediate fact. Rewrite `this` using `[Over.comp_left, Over.comp_left]`. Conclude with `this`. Establish `hE : eSec (thickObj R (maximalIdeal R) 0 D.toPre.P.A) ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ eSec D.toPre.P.A` using `GlobalTheory.UnitValue.eSec_pullback_fst _ _`.

Establish `hz' : z.left ≫ (splitTorus (Sp A) D.toPre.X).hom = spMap f` using `Over.w z`. Establish `hfa : spMap f ≫ spMap a = spMap (f.comp a)`. Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Simplify using `only [y₂, Category.assoc]`.

Rewrite using `[reassoc_of% hk, hE, ← Category.assoc (GlobalTheory.SplitTorus.bcMap _ _), GlobalTheory.SplitTorus.bcMap_hom, Category.assoc, reassoc_of% (GlobalTheory.TorusPart.thickPt_thick hρ), reassoc_of% hz', reassoc_of% hfa]`. Both sides reduce to the same expression. Introduce `χ w J hJ`. Rewrite using `[hv χ w J hJ]`. Establish `l₁ : val (g₀.s χ) h.left w J = gm (𝟙 _) w ⊤ (unitOn (τ (Multiplicative.ofAdd χ)))`.

Establish `c₁` using `val_corr hJ (hpull.2 χ) (𝟙 _)`. Rewrite `c₁` using `[val_pull hJ, Category.id_comp]`. Conclude with `c₁.symm.trans (GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) (𝟙 _) hJ)`. Rewrite using `[l₁]`. Set `Z₀ : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))` to `Over.mk ((z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X) ≫ (splitTorus _ D.toPre.X).hom)`.

Set `τ' : Z₀ ⟶ splitTorus _ D.toPre.X` to `Over.homMk (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X) rfl`. Establish `k` using `GlobalTheory.TorusCoord.val_t_act (U.gt 0) τ' 1 χ (𝟙 Z₀.left) w J hJ`. Establish `k₁ : 𝟙 Z₀.left ≫ (τ' ≫ (U.gt 0).i * 1).left = y₂`. Rewrite using `[_root_.mul_one, Category.id_comp, Over.comp_left]`. Simplify using `only [τ', y₂, Over.homMk_left, Category.assoc]`.

Establish `k₂ : val ((U.gt 0).t χ) (𝟙 Z₀.left ≫ (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 G).left) w J = 1`. Establish `e : (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 G).left = Z₀.hom ≫ eSec (thickObj R (maximalIdeal R) 0 G)`. Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression. Rewrite using `[e, Category.id_comp, ← val_pull hJ, val_corr hJ ((U.gt 0).t_unit χ), val_one]`.

Establish `k₃ : GlobalTheory.splitTorusPointsEquiv _ D.toPre.X Z₀ τ' (Multiplicative.ofAdd χ) = unitOn (τ (Multiplicative.ofAdd χ))`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[← hz χ, GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val]`. Simplify using `only [τ', Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, GlobalTheory.SplitTorus.bcMap_appTop_chi]`. Rewrite `k` using `[k₁, k₂, k₃, _root_.mul_one]`.

Conclude with `k.symm`.
-/
theorem eq_torus_of_classify (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (D : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A₁ G)
    (N : Over (Sp R)) (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G) (hform : FormalEq U.toUnifPre x₀ g₀)
    (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (f : A →+* A')
    (G₀ : Over (Sp A)) [GrpObj G₀] [IsCommMonObj G₀] (m₀ : G₀.left ⟶ G.left) (hm₀ : IsGrpPullback G₀ G (spMap a) m₀)
    (τ : Multiplicative D.toPre.X →* A'ˣ) (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) D.toPre.X)
    (hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ)))
    (g : GtPt D.toPre (Over.mk (spMap (f.comp a)))) (hg : ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))))
    (h : Over.mk (spMap (f.comp a)) ⟶ N) (hpull : GtPt.IsPull h.left g₀ g) :
    h.left ≫ x₀.left = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero ha) hm₀).left ≫ m₀ := by
  have ha' : ∀ x ∈ maximalIdeal R, (f.comp a) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, ha x hx, map_zero]
  have hρ := GlobalTheory.TorusPart.map_pow_one_eq_zero ha
  have hρ' := GlobalTheory.TorusPart.map_pow_one_eq_zero ha'
  have eR : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero ha) hm₀).left ≫ m₀ =
      (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X ≫ (U.gt 0).i.left) ≫
        pullback.fst G.hom (thick R (maximalIdeal R) 0) := by
    rw [Over.comp_left, Category.assoc]
    have k := GlobalTheory.TorusPart.gtTorus_left (U.gt 0) hρ hm₀
    exact (congrArg (z.left ≫ ·) k).trans (by simp only [Category.assoc])
  have hN : (h.left ≫ x₀.left) ≫ G.hom = GlobalTheory.TorusPart.thickPt 0 hρ' ≫ thick R (maximalIdeal R) 0 := by
    rw [GlobalTheory.TorusPart.thickPt_thick, Category.assoc, Over.w x₀, Over.w h]; rfl
  let y₁ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 G).left :=
    pullback.lift (h.left ≫ x₀.left) (GlobalTheory.TorusPart.thickPt 0 hρ') hN
  let y₂ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 G).left :=
    z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X ≫ (U.gt 0).i.left
  have e₁ : h.left ≫ x₀.left = y₁ ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) :=
    (pullback.lift_fst _ _ _).symm
  have hP := (GlobalTheory.TorsionFormCompare.formalEq_iff U.toUnifPre x₀ g₀).1 hform
  have hc := hP 0 (Sp A') h.left y₁ e₁.symm
  obtain ⟨hb, hv⟩ := (GlobalTheory.FormalPoint.hasCoords_iff _ 0 g₀ h.left y₁).1 hc
  suffices hy : y₁ = y₂ by rw [eR, e₁, hy]
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt 0) y₁ y₂ ?_ ?_
  · rw [hb, ← hpull.1, (hg 0).1, GlobalTheory.TorusCoord.pG_left]
    have hk : (U.gt 0).i.left ≫ (U.gt 0).q.left =
        (splitTorus _ D.toPre.X).hom ≫ eSec (thickObj R (maximalIdeal R) 0 D.toPre.P.A) := by
      have := congrArg Over.Hom.left (U.gt 0).isKernel.w
      rw [Over.comp_left, Over.comp_left] at this
      exact this
    have hE : eSec (thickObj R (maximalIdeal R) 0 D.toPre.P.A) ≫
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        thick R (maximalIdeal R) 0 ≫ eSec D.toPre.P.A :=
      GlobalTheory.UnitValue.eSec_pullback_fst _ _
    have hz' : z.left ≫ (splitTorus (Sp A) D.toPre.X).hom = spMap f := Over.w z
    have hfa : spMap f ≫ spMap a = spMap (f.comp a) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    simp only [y₂, Category.assoc]
    rw [reassoc_of% hk, hE, ← Category.assoc (GlobalTheory.SplitTorus.bcMap _ _), GlobalTheory.SplitTorus.bcMap_hom,
      Category.assoc, reassoc_of% (GlobalTheory.TorusPart.thickPt_thick hρ), reassoc_of% hz', reassoc_of% hfa]
    rfl
  · intro χ w J hJ
    rw [hv χ w J hJ]
    have l₁ : val (g₀.s χ) h.left w J = gm (𝟙 _) w ⊤ (unitOn (τ (Multiplicative.ofAdd χ))) := by
      have c₁ := val_corr hJ (hpull.2 χ) (𝟙 _)
      rw [val_pull hJ, Category.id_comp] at c₁
      exact c₁.symm.trans (GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) (𝟙 _) hJ)
    rw [l₁]
    let Z₀ : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :=
      Over.mk ((z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X) ≫
        (splitTorus _ D.toPre.X).hom)
    let τ' : Z₀ ⟶ splitTorus _ D.toPre.X :=
      Over.homMk (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) D.toPre.X) rfl
    have k := GlobalTheory.TorusCoord.val_t_act (U.gt 0) τ' 1 χ (𝟙 Z₀.left) w J hJ
    have k₁ : 𝟙 Z₀.left ≫ (τ' ≫ (U.gt 0).i * 1).left = y₂ := by
      rw [_root_.mul_one, Category.id_comp, Over.comp_left]
      simp only [τ', y₂, Over.homMk_left, Category.assoc]
    have k₂ : val ((U.gt 0).t χ) (𝟙 Z₀.left ≫ (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 G).left) w J = 1 := by
      have e : (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 G).left = Z₀.hom ≫ eSec (thickObj R (maximalIdeal R) 0 G) := by
        rw [Hom.one_def, Over.comp_left]; rfl
      rw [e, Category.id_comp, ← val_pull hJ, val_corr hJ ((U.gt 0).t_unit χ), val_one]
    have k₃ : GlobalTheory.splitTorusPointsEquiv _ D.toPre.X Z₀ τ' (Multiplicative.ofAdd χ) =
        unitOn (τ (Multiplicative.ofAdd χ)) := by
      refine Units.ext ?_
      rw [← hz χ, GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val]
      simp only [τ', Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        GlobalTheory.SplitTorus.bcMap_appTop_chi]
    rw [k₁, k₂, k₃, _root_.mul_one] at k
    exact k.symm

end TorusPoint

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Introduce `R _ _ _ hB G _ _ hG D A U k hk`. Take `⟨hR, hC⟩` from `hB`. Use `haveI := hC`. Take `⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩` from `exists_torsion_toG R hR G D A U k hk`. Set `u : ∀ (B : Type) [CommRing B] (_ : Multiplicative D.toPre.X →* Bˣ), D.toPre.X →+ Additive Γ(Sp B, ⊤)ˣ` to `fun B _ τ => AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by`.

Simplify using `only [ofAdd_add, map_mul, unitOn, ofMul_mul])`. Establish `hu : ∀ (B : Type) [CommRing B] (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → k • u B τ = 0`. Introduce `B _ τ hτ`. Use `AddMonoidHom.ext fun χ => Additive.toMul.injective ?_` and prove the remaining obligations. Establish `e : (τ (Multiplicative.ofAdd χ)) ^ k = 1` using `by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]`.

Simplify using `only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e, map_one, AddMonoidHom.zero_apply, toMul_zero]`. Establish `ex : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), ∃ g : GtPt D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))`. Introduce `B _ a τ`. Take `⟨g, hg⟩` from `GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := Over.mk (spMap a)) (u B τ)`. Conclude with `⟨g, hg⟩`.

Use `choose gT hgT using ex`. Establish `ex₂ : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT B a τ)`. Introduce `B _ a τ hτ`. Take `⟨g', h₁, h₂⟩` from `GlobalTheory.TorusTorsion.exists_nsmul_zero k (u B τ) (hu B τ hτ) (T := Over.mk (spMap a)) (g := gT B a τ) (hgT B a τ)`. Conclude with `hU _ _ ⟨g', h₁, h₂⟩`.

Use `choose hT hhT hTu using ex₂`. Use `⟨fun B _ a τ hτ => hT B a τ hτ ≫ x₀, fun B _ a τ hτ => ?_, fun B B' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun B B' _ _ a ha a' f G₀ _ _ m₀ hm₀ τ hτ z ha' hz => ?_, fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩` and prove the remaining obligations. Use `show (hT B a τ hτ ≫ x₀) ^ k = 1`. Rewrite using `[← MonObj.comp_pow, htors, MonObj.comp_one]`. Substitute `ha` using the available equality.

Set `ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a)` to `Over.homMk (spMap f) (GlobalTheory.ToricTorsionSec.spMap_comp a f).symm`. Establish `hρ : GtPt.IsPull ρ.left (gT B a τ) (gT B' (f.comp a) τ')` using `GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT B a τ) (hgT B' _ τ') fun χ => by`. Use `(GlobalTheory.ToricTorsionSec.appTop_unitOn f _).trans ?_` and prove the remaining obligations. Use `congr 2`. Conclude with `Units.ext (hτf _).symm`.

Establish `e` using `hTu B' _ τ' hτ' (ρ ≫ hT B a τ hτ) (GlobalTheory.ToricTorsionSec.isPull_trans (hhT B a τ hτ) hρ)`. Use `show (hT B' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT B a τ hτ ≫ x₀).left`. Rewrite using `[← e]`. Both sides reduce to the same expression. Substitute `ha'` using the available equality.

Conclude with `eq_torus_of_classify R G D A U N g₀ x₀ hform B B' a ha f G₀ m₀ hm₀ τ z hz (gT B' _ τ) (hgT B' _ τ) (hT B' _ τ hτ) (hhT B' _ τ hτ)`. Substitute `ha` using the available equality. Establish `hx : OverGen F N (hT F _ τ hτ).left` using `(Over.w (hT F _ τ hτ)).trans (GlobalTheory.ToricTorsionSec.spMap_comp _ _)`. Establish `hp` using `GlobalTheory.ToricTorsionSec.isPullF_trans (hhT F _ τ hτ) (GlobalTheory.ToricTorsionSec.isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)`. Rewrite `hp` using `[Category.id_comp]`.

Conclude with `generic R hR G hG D A U k hk N g₀ x₀ hfin htors hform F _ hx q hq hp`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k →
    ∃ s : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G),
      (∀ (B : Type) [CommRing B] (a : R →+* B) τ h, s B a τ h ^ k = 1) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (a' : R →+* B') (f : B →+* B') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : B') = f (τ χ : B)) → (s B' a' τ' h').left = spMap f ≫ (s B a τ h).left) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* B') (f : B →+* B')
        (G₀ : Over (Sp B)) [GrpObj G₀] [IsCommMonObj G₀] (m₀ : G₀.left ⟶ G.left) (hm₀ : IsGrpPullback G₀ G (spMap a) m₀) τ h
        (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero ha) hm₀).left ≫ m₀) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        ∃ x : TFK (R := R) F ⟶ A.A, x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (s F a τ h).left ∧
          QkToAkU U.toUnifPre F k q x := by
  intro R _ _ _ hB G _ _ hG D A U k hk
  obtain ⟨hR, hC⟩ := hB
  haveI := hC
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := exists_torsion_toG R hR G D A U k hk
  let u : ∀ (B : Type) [CommRing B] (_ : Multiplicative D.toPre.X →* Bˣ),
      D.toPre.X →+ Additive Γ(Sp B, ⊤)ˣ := fun B _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (B : Type) [CommRing B] (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → k • u B τ = 0 := by
    intro B _ τ hτ
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  have ex : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ),
      ∃ g : GtPt D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))) := by
    intro B _ a τ
    obtain ⟨g, hg⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := Over.mk (spMap a)) (u B τ)
    exact ⟨g, hg⟩
  choose gT hgT using ex
  have ex₂ : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 →
      ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT B a τ) := by
    intro B _ a τ hτ
    obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u B τ) (hu B τ hτ) (T := Over.mk (spMap a))
      (g := gT B a τ) (hgT B a τ)
    exact hU _ _ ⟨g', h₁, h₂⟩
  choose hT hhT hTu using ex₂
  refine ⟨fun B _ a τ hτ => hT B a τ hτ ≫ x₀, fun B _ a τ hτ => ?_,
    fun B B' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun B B' _ _ a ha a' f G₀ _ _ m₀ hm₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩
  · show (hT B a τ hτ ≫ x₀) ^ k = 1
    rw [← MonObj.comp_pow, htors, MonObj.comp_one]
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) :=
      Over.homMk (spMap f) (GlobalTheory.ToricTorsionSec.spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT B a τ) (gT B' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT B a τ) (hgT B' _ τ') fun χ => by
        refine (GlobalTheory.ToricTorsionSec.appTop_unitOn f _).trans ?_
        congr 2
        exact Units.ext (hτf _).symm
    have e := hTu B' _ τ' hτ' (ρ ≫ hT B a τ hτ) (GlobalTheory.ToricTorsionSec.isPull_trans (hhT B a τ hτ) hρ)
    show (hT B' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT B a τ hτ ≫ x₀).left
    rw [← e]
    rfl
  · subst ha'
    exact eq_torus_of_classify R G D A U N g₀ x₀ hform B B' a ha f G₀ m₀ hm₀ τ z hz (gT B' _ τ) (hgT B' _ τ)
      (hT B' _ τ hτ) (hhT B' _ τ hτ)
  · subst ha
    have hx : OverGen F N (hT F _ τ hτ).left :=
      (Over.w (hT F _ τ hτ)).trans (GlobalTheory.ToricTorsionSec.spMap_comp _ _)
    have hp := GlobalTheory.ToricTorsionSec.isPullF_trans (hhT F _ τ hτ)
      (GlobalTheory.ToricTorsionSec.isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    exact generic R hR G hG D A U k hk N g₀ x₀ hfin htors hform F _ hx q hq hp

end Main

end GlobalTheory.ToricTorsionSecUnif
