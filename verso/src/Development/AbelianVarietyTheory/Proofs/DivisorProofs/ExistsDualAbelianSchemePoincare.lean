import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualRepresentableAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDimsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualExist

/- English proof (translation)
Take `⟨B, b, P, hR, hG⟩` from `h`. Use `⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨x, ⟨hx, hxN⟩, hu⟩` from `hR.univ T (t ≫ e.inv) N hN`. Use `⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩, fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩` and prove the remaining obligations. Rewrite using `[← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]`.

Establish `: IsIso e.inv.left` using `inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)`. Establish `sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left` using `IsPullback.of_horiz_isIso ⟨by`. Rewrite using `[Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩`. Establish `hp` using `hG.proper`. Use `smoothOfRelativeDimension_isStableUnderBaseChange g` as an intermediate fact.

Rewrite using `[Over.comp_left]`. Conclude with `⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth, MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩`.
-/
theorem hasRep_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] {g : ℕ} {S₁ S₂ : Over S} (e : S₁ ≅ S₂)
    (h : HasRep A g S₁) : HasRep A g S₂ := by
  obtain ⟨B, b, P, hR, hG⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩
  · obtain ⟨x, ⟨hx, hxN⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩,
      fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩
    rw [← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)
    have sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩
    have hp := hG.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [Over.comp_left]
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩

/- English proof (translation)
Set `A' : Over (Sp Γ(S, V))` to `(Over.pullback hV.fromSpec).obj A`. Use `letI : GrpObj A' := Functor.grpObjObj`. Establish `hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec)` using `isGrpPullback_pullback A hV.fromSpec`. Establish `hA' : IsAbelianScheme A'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb`. Establish `hg' : SmoothOfRelativeDimension g A'.hom`.

Establish `sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec) (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv) (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι])) (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv` using `IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)`. Use `haveI := smoothOfRelativeDimension_isStableUnderBaseChange g`. Conclude with `MorphismProperty.of_isPullback sq hg`. Establish `h1` using `((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (GlobalTheory.T.abelianScheme_dual_representable_affine_base _ A' g hA' hg')`. Use `hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1` and prove the remaining obligations.

Use `show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec`. Rewrite using `[Category.id_comp, IsAffineOpen.isoSpec_inv_ι]`.
-/
theorem hasRep_affineOpen {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {V : S.Opens}
    (hV : IsAffineOpen V) (g : ℕ) (hg : SmoothOfRelativeDimension g (pullback.snd A.hom V.ι)) :
    HasRep A g (Over.mk V.ι) := by
  let A' : Over (Sp Γ(S, V)) := (Over.pullback hV.fromSpec).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    have sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec)
        (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv)
        (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι]))
        (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback sq hg
  have h1 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (GlobalTheory.T.abelianScheme_dual_representable_affine_base _ A' g hA' hg')
  refine hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1
  show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec
  rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι]

/- English proof (translation)
Introduce `S A _ hA`. Use `choose V g hV hsV hgV using GlobalTheory.T.abelianScheme_locally_constant_relDim S A hA`. Establish `cov : ∀ s : S, ∃ i, s ∈ V i` using `fun s => ⟨s, hsV s⟩`. Take `⟨B, P, hR, hGood⟩` from `GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))`. Take `⟨inst, hcomm, hD, -⟩` from `GlobalTheory.T.representing_additiveFamilies_isDual_comm S A B P hR`.

Use `⟨B, inst, P, ?_, ?_, hD⟩` and prove the remaining obligations. Establish `hU : iSup V = ⊤` using `eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩`. Establish `: IsZariskiLocalAtTarget (@GeometricallyConnected.{0})`. Rewrite using `[GeometricallyConnected.eq_geometrically]`. Use `infer_instance`.

Establish `: IsZariskiLocalAtTarget @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)`. Establish `sq` using `fun i => IsPullback.of_hasPullback B.hom (V i).ι`. Conclude with `{ comm := hcomm smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _ proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper geomConnected := …`. Establish `: GeometricallyConnected A.hom` using `hA.geomConnected`. Conclude with `GlobalTheory.T.relDimPreserved_of_equal_local_relDims S A B inferInstance S V g cov hgV fun i => (hGood i).smooth`.
-/
theorem exists_dual : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  intro S A _ hA
  choose V g hV hsV hgV using GlobalTheory.T.abelianScheme_locally_constant_relDim S A hA
  have cov : ∀ s : S, ∃ i, s ∈ V i := fun s => ⟨s, hsV s⟩
  obtain ⟨B, P, hR, hGood⟩ :=
    GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))
  obtain ⟨inst, hcomm, hD, -⟩ := GlobalTheory.T.representing_additiveFamilies_isDual_comm S A B P hR
  refine ⟨B, inst, P, ?_, ?_, hD⟩
  · have hU : iSup V = ⊤ := eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩
    have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    have sq := fun i => IsPullback.of_hasPullback B.hom (V i).ι
    exact
      { comm := hcomm
        smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by
          haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _
        proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper
        geomConnected := GlobalTheory.CoverGlue.of_isPullback_cover @GeometricallyConnected hU sq fun i => (hGood i).conn }
  · have : GeometricallyConnected A.hom := hA.geomConnected
    exact GlobalTheory.T.relDimPreserved_of_equal_local_relDims S A B inferInstance S V g cov hgV fun i => (hGood i).smooth

end GlobalTheory.DualExist
