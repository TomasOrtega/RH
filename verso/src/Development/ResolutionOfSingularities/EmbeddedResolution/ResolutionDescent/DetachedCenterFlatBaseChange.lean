import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem map_eq_ker_subschemeι_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    I.map f = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

/- English proof (translation)
Establish `h1 : S'.ambientCenter j = (S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le)` using `F.center_eq j hj`. Establish `h2 : F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j) = S'.strictTransformι j ≫ F.levelMap j hj.le` using `F.strictTransformComparison_comp_strictTransformι j hj.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Use `_ = (S.ambientCenter (F.reindex j)).comap (S'.strictTransformι j ≫ F.levelMap j hj.le) := by`.

Simplify using `[Scheme.IdealSheafData.comap_comp]`. Use `_ = (S.ambientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)) := by rw [h2]`. Use `_ = ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).comap (F.strictTransformComparison j hj.le) := by simp [Scheme.IdealSheafData.comap_comp]`. Use `_ = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := rfl`.
-/
theorem comapAmbientCenter_eq_comap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.comapAmbientCenter j =
      (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have h1 : S'.ambientCenter j
      = (S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le) := F.center_eq j hj
  have h2 : F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι j ≫ F.levelMap j hj.le := F.strictTransformComparison_comp_strictTransformι j hj.le
  calc S'.comapAmbientCenter j = (S'.ambientCenter j).comap (S'.strictTransformι j) := rfl
    _ = ((S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le)).comap (S'.strictTransformι j) := by
        rw [h1]
    _ = (S.ambientCenter (F.reindex j)).comap (S'.strictTransformι j ≫ F.levelMap j hj.le) := by
        simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.ambientCenter (F.reindex j)).comap
          (F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)) := by rw [h2]
    _ = ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).comap
          (F.strictTransformComparison j hj.le) := by simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := rfl

/- English proof (translation)
Establish `hflat : AlgebraicGeometry.Flat (F.strictTransformComparison j hj.le)` using `F.flat_strictTransformComparison j hj.le`. Establish `hnoe : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j))` using `S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)`. Establish `hqc : AlgebraicGeometry.QuasiCompact (S.detachedClosureCompl (F.reindex j)).ι` using `⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩`. Establish `hpb : IsPullback (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j)) ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι) (S.detachedClosureCompl (F.reindex j)).ι (F.strictTransformComparison j hj.le)` using `AlgebraicGeometry.isPullback_morphismRestrict _ _`. Establish `key` using `comap_map_eq_map_comap_of_isPullback hpb ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι)`.

Establish `htrace : S'.comapAmbientCenter j = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le)` using `F.comapAmbientCenter_eq_comap j hj`. Establish `hcomap : ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι).comap (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j)) = (S'.comapAmbientCenter j).comap ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F …`. Rewrite using `[htrace, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hpb.w]`. Rewrite using `[S'.centerOffDetached_eq j, S.centerOffDetached_eq (F.reindex j), ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp (S'.detachedClosureCompl j).ι, ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subsche …`.
-/
theorem centerOffDetached_eq_comap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.centerOffDetached j =
      (S.centerOffDetached (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have hflat : AlgebraicGeometry.Flat (F.strictTransformComparison j hj.le) := F.flat_strictTransformComparison j hj.le
  have hnoe : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have hqc : AlgebraicGeometry.QuasiCompact (S.detachedClosureCompl (F.reindex j)).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hpb : IsPullback (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
      ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι)
      (S.detachedClosureCompl (F.reindex j)).ι (F.strictTransformComparison j hj.le) :=
    AlgebraicGeometry.isPullback_morphismRestrict _ _
  have key := comap_map_eq_map_comap_of_isPullback hpb
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι)
  have htrace : S'.comapAmbientCenter j
      = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) :=
    F.comapAmbientCenter_eq_comap j hj
  have hcomap :
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι).comap
          (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
        = (S'.comapAmbientCenter j).comap
            ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι) := by
    rw [htrace, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hpb.w]
  rw [S'.centerOffDetached_eq j, S.centerOffDetached_eq (F.reindex j),
    ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp (S'.detachedClosureCompl j).ι, ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp (S.detachedClosureCompl (F.reindex j)).ι,
    F.detachedClosureCompl_eq_preimage j hj, key, hcomap]

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
