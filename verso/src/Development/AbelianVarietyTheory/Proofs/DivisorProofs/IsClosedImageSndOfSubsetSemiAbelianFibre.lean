import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ G _ hG x hx hxc N hN hNZ`. Establish `hlft : LocallyOfFiniteType G.hom` using `by haveI := hG.smooth; infer_instance`. Establish `hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom)` using `GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc`. Use `set k := G.left.fromSpecResidueField x`. Use `set f := G.hom`.

Set `i` to `pullback.snd k (pullback.fst f f)`. Establish `hrange : Set.range i = (pullback.fst f f) ⁻¹' {x}`. Simplify using `only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]`. Establish `hcomp : i ≫ pullback.snd f f = (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f` using `(pullbackRightPullbackFstIso_hom_snd f f k).symm`. Establish `hcl : IsClosedMap (i ≫ pullback.snd f f)`.

Rewrite using `[hcomp]`. Use `haveI := hfin`. Use `haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance`. Conclude with `((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap`. Establish `hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N)`.

Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]`. Both sides reduce to the same expression. Rewrite using `[hrange]`. Conclude with `hNZ`. Rewrite using `[hNi]`.

Conclude with `hcl _ (hN.preimage i.continuous)`.
-/
theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
