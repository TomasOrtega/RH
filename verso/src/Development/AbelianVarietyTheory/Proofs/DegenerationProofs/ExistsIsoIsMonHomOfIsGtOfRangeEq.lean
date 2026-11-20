import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusPointEqOneOfAxes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

/- English proof (translation)
Use `le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)` and prove the remaining obligations. Rewrite using `[← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]`. Conclude with `f.range_subset_ker_support`.
-/
theorem ker_le_ker_of_range_subset_of_isReduced {X T Y : Scheme.{0}} [IsReduced T] (f : X ⟶ Y)
    [IsClosedImmersion f] (g : T ⟶ Y) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g
    ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact f.range_subset_ker_support

/- English proof (translation)
Introduce `k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1`. Establish `hs` using `(UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1`. Establish `hs'` using `(UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1`. Establish `: IsReduced G.left` using `isReduced_of_smooth_of_isReduced G.hom`. Establish `: IsReduced G'.left` using `isReduced_of_smooth_of_isReduced G'.hom`.

Establish `hk : f'.left.ker = f.left.ker` using `le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le) (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)`. Use `IsClosedImmersion.isIso_lift f'.left f.left hk` as an intermediate fact. Establish `hl` using `IsClosedImmersion.lift_fac f'.left f.left hk.le`. Set `e : G ≅ G'` to `Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by`. Rewrite using `[asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])`.

Establish `he : e.hom ≫ f' = f` using `Over.OverMorphism.ext hl`. Establish `: Mono f'` using `Over.mono_of_mono_left f'`. Use `⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono f', Category.assoc, he, h1]`.
-/
theorem exists_iso_isMonHom_of_isGt_of_range_eq :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Over (Sp k)) (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (f : G ⟶ Y) (f' : G' ⟶ Y), E.IsGt G → E'.IsGt G' → IsClosedImmersion f.left → IsClosedImmersion f'.left → Set.range f.left = Set.range f'.left → η[G] ≫ f = η[G'] ≫ f' → ∃ e : G ≅ G', IsMonHom e.hom ∧ e.hom ≫ f' = f := by
  intro k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1
  have hs := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1
  have hs' := (UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have hk : f'.left.ker = f.left.ker :=
    le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le)
      (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)
  have := IsClosedImmersion.isIso_lift f'.left f.left hk
  have hl := IsClosedImmersion.lift_fac f'.left f.left hk.le
  let e : G ≅ G' := Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by
    rw [asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])
  have he : e.hom ≫ f' = f := Over.OverMorphism.ext hl
  have : Mono f' := Over.mono_of_mono_left f'
  refine ⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩
  rw [← cancel_mono f', Category.assoc, he, h1]

end GlobalTheory
