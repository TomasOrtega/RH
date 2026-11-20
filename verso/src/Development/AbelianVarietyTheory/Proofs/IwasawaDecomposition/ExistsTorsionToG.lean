import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.WholeBaseFinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

/- English proof (translation)
Take `⟨_, -, -, hc⟩` from `hR`. Establish `hL` using `abelianSchemeLaws_all.1`. Take `⟨Gt, _, _, hH⟩` from `exists_isGt hL.globalFns (splitExt P.D.toPre)`. Take `⟨Φ, hΦ⟩` from `exists_points hL.globalFns hH`. Establish `hΦ : Represents Φ` using `hΦ`.

Establish `hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom`. Take `⟨h₁, h₂, -⟩` from `hL.mulN _ P.D.toPre.P k hk`. Establish `h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left` using `h₁`. Establish `h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left` using `h₂`. Rewrite `h₁'`, `h₂'` using `[← MulEtaleDvr.mulN_eq_pow]`.

Establish `Q` using `MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k`. Conclude with `isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')`. Take `⟨hf, hl⟩` from `hfin`. Take `⟨J, hJ⟩` from `exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ`. Establish `hN` using `isAdicColimit_of_isFinite hc (torsion Gt k)`.

Use `⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl, (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_, (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(Φ T).surjective g`. Establish `hx` using `(tors_iff hΦ k x).1 hg`. Use `⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩` and prove the remaining obligations. Rewrite using `[torsionLift_ι]`.

Conclude with `(isPull_iff_comp hΦ _ _ _).1 hh`. Rewrite using `[← map_pow, torsionι_pow, map_one]`.
-/
theorem exists_torsion_toG (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
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
Establish `hL` using `firstFiveLaws`. Use `hfin` as an intermediate fact. Take `⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩` from `exists_normal_point R hR F N x hx`. Establish `hφ : Function.Injective φ` using `fun a b e => IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))`. Take `⟨D', hD, A', U', hU⟩` from `UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U`.

Establish `hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ` using `hξ.trans (Category.id_comp _).symm`. Take `⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T'` from `𝟙_ _) ξ g₀ gp := ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr (T' := 𝟙_ _) ξ hh g₀`. Set `x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G` to `Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh)) (pullback.lift_snd _ _ _)`. Establish `e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left` using `pullback.lift_fst _ _ _`. Establish `e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left` using `(congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁`.

Establish `gG` using `isGrpPullback_pullback t.G (spMap φ)`. Establish `hk₁ : x₁ ^ k = 1` using `ConstGrp.push_injective gG _ (by`. Set `ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N` to `Over.homMk ξ hh`. Establish `e : pushHom gG _ x₁ = ρ ≫ x₀` using `Over.OverMorphism.ext e₁`. Rewrite using `[map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])`.

Establish `hp` using `isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)`. Take `⟨g', hg'⟩` from `FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp`. Set `y : TFK (R` to `R) F ⟶ (Over.pullback (jK R)).obj t.G := Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F) (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)`. Establish `hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = ((jFK (R` using `R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by`. Rewrite using `[← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.

Conclude with `pullback.lift_fst _ _ _`. Use `⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁ (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩` and prove the remaining obligations. Set `xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G))` to `Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)) (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))`. Establish `hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁` using `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`. Establish `c` using `hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)`.

Conclude with `⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩`. Rewrite using `[hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]`. Conclude with `Category.assoc _ _ _`.
-/
theorem generic (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N)
    (x₀ : N ⟶ t.G) (hfin : IsFinite N.hom) (htors : x₀ ^ k = 1) (hform : FormalEq P.U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left) (hx : OverGen F N x)
    (q : QkPt P.D.toPre F k) (hq : q.y = 0) (hg : GtPt.IsPullF F x g₀ q.g) : IsImage P F k q (x ≫ x₀.left) := by
  have hL := firstFiveLaws
  have := hfin
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.WholeBaseFinitePart
