import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymExtendDvr

/- English proof (translation)
Establish `: IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget S).map e.hom))`. Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Set `u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T` to `Over.homMk (𝟙 _) (by simp)`. Establish `e₁ : x₀ = u ≫ x ≫ e.hom` using `Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)`. Establish `e₂ : y₀ = u ≫ y ≫ e.hom` using `Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)`.

Rewrite using `[e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]`. Conclude with `Category.id_comp _`.
-/
theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
  have e₁ : x₀ = u ≫ x ≫ e.hom := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have e₂ : y₀ = u ≫ y ≫ e.hom := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

/- English proof (translation)
Introduce `ext V _ _ _ A G _ _ hG H gen hgen L hL`. Use `hG.smooth` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Establish `hc : IsCommMonObj ((Over.pullback (jK V)).obj G)` using `Functor.isCommMonObj_obj`. Establish `hA : (A.L.pull gen.hom.left).IsLB` using `pull_isLB A.isLB _`.

Establish `H' : HypS ((Over.pullback (jK V)).obj G) (A.L.pull gen.hom.left)` using `GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A _ (𝟙 _) gen.hom.left A.L _ A.isLB hA (isGrpPullback_of_iso gen) ((GlobalTheory.PrimNorm.lbIso_iff A.isLB _ _ _ _).2 rfl) H`. Establish `: IsOpenImmersion (jK V)` using `GlobalTheory.DvrModel.isOpenImmersion_generic (K := FractionRing V) (f := 𝟙 _) (j := jK V) (fK := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)`. Use `GlobalTheory.SymExtend.hypS_extend (GlobalTheory.IsNormalScheme.pred _) (isGrpPullback_pullback G (jK V)) ?_ _ L hA hL.symm H'` and prove the remaining obligations. Introduce `α hα`. Take `⟨F, ⟨hF, eF⟩, u⟩` from `ext V (FractionRing V) G G hG hG α hα`.

Establish `c : ∀ F : G ⟶ G, ((Over.pullback (jK V)).map F).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ F.left` using `fun F => pullback.lift_fst _ _ _`. Use `⟨F, ⟨hF, ?_⟩, fun F' h' => u F' ⟨h'.1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← eF]`. Conclude with `(c F).symm`. Use `Over.OverMorphism.ext (pullback.hom_ext ((c F').trans h'.2) ?_)` and prove the remaining obligations.

Conclude with `(Over.w ((Over.pullback (jK V)).map F')).trans (Over.w α).symm`.
-/
theorem hypS_of_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  intro ext V _ _ _ A G _ _ hG H gen hgen L hL
  have := hG.smooth
  have := hG.geomConnected
  have hc : IsCommMonObj ((Over.pullback (jK V)).obj G) := Functor.isCommMonObj_obj
  have hA : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have H' : HypS ((Over.pullback (jK V)).obj G) (A.L.pull gen.hom.left) :=
    GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A _ (𝟙 _) gen.hom.left A.L _ A.isLB hA (isGrpPullback_of_iso gen)
      ((GlobalTheory.PrimNorm.lbIso_iff A.isLB _ _ _ _).2 rfl) H
  have : IsOpenImmersion (jK V) := GlobalTheory.DvrModel.isOpenImmersion_generic (K := FractionRing V) (f := 𝟙 _)
    (j := jK V) (fK := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  refine GlobalTheory.SymExtend.hypS_extend (GlobalTheory.IsNormalScheme.pred _) (isGrpPullback_pullback G (jK V)) ?_ _ L hA hL.symm H'
  intro α hα
  obtain ⟨F, ⟨hF, eF⟩, u⟩ := ext V (FractionRing V) G G hG hG α hα
  have c : ∀ F : G ⟶ G, ((Over.pullback (jK V)).map F).left ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ F.left := fun F => pullback.lift_fst _ _ _
  refine ⟨F, ⟨hF, ?_⟩, fun F' h' => u F' ⟨h'.1, ?_⟩⟩
  · rw [← eF]
    exact (c F).symm
  · refine Over.OverMorphism.ext (pullback.hom_ext ((c F').trans h'.2) ?_)
    exact (Over.w ((Over.pullback (jK V)).map F')).trans (Over.w α).symm

end GlobalTheory.SymExtendDvr
