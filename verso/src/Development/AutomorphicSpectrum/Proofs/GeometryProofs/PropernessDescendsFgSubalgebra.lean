import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFgIsClosedPreimageRange
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    pullback (i ≫ q) g ⟶ pullback q g :=
  pullback.lift (pullback.fst (i ≫ q) g ≫ i) (pullback.snd (i ≫ q) g)
    (by rw [Category.assoc, pullback.condition])

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem baseChangeMap_snd {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.snd q g = pullback.snd (i ≫ q) g :=
  pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem baseChangeMap_fst {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    baseChangeMap i q g ≫ pullback.fst q g = pullback.fst (i ≫ q) g ≫ i :=
  pullback.lift_fst _ _ _

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := pullback.snd q g) (h₂₂ := q) (v₁₃ := g) ?_ (baseChangeMap_fst i q g) (IsPullback.of_hasPullback q g).flip` and prove the remaining obligations. Rewrite using `[baseChangeMap_snd]`. Conclude with `(IsPullback.of_hasPullback (i ≫ q) g).flip`.
-/
theorem isPullback_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    IsPullback (baseChangeMap i q g) (pullback.fst (i ≫ q) g) (pullback.fst q g) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd q g) (h₂₂ := q) (v₁₃ := g) ?_
    (baseChangeMap_fst i q g) (IsPullback.of_hasPullback q g).flip
  rw [baseChangeMap_snd]
  exact (IsPullback.of_hasPullback (i ≫ q) g).flip

/- English proof (translation)
Establish `h` using `isPullback_baseChangeMap i q g`. Rewrite using `[← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]`.
-/
theorem range_baseChangeMap {X P T B : Scheme.{0}} (i : X ⟶ P) (q : P ⟶ B) (g : T ⟶ B) :
    Set.range (baseChangeMap i q g) = pullback.fst q g ⁻¹' Set.range i := by
  have h := isPullback_baseChangeMap i q g
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

/- English proof (translation)
Take `⟨N, i, hi, -, rfl⟩` from `hp`. Establish `hq : IsProper (PSpace.str k N)` using `isProper_str k N`. Establish `hcl : IsClosed (pullback.fst (PSpace.str k N) (spMap (algebraMap k V)) ⁻¹' Set.range i)`. Rewrite using `[← range_baseChangeMap]`. Establish `h1 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V)) ≫ pullback.snd (PSpace.str k N) (spMap (algebraMap k V)))`.

Rewrite using `[baseChangeMap_snd]`. Conclude with `hV`. Establish `h2 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V)))` using `IsProper.of_comp _ (pullback.snd (PSpace.str k N) (spMap (algebraMap k V)))`. Conclude with `(baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))).isClosedMap.isClosed_range`. Take `⟨R, hR, hclR⟩` from `exists_fg_isClosed_preimage_range k V X (PSpace k N) i (PSpace.str k N) hi inferInstance inferInstance hcl`.

Use `⟨R, hR, ?_⟩` and prove the remaining obligations. Rewrite `hclR` using `[← range_baseChangeMap]`. Establish `hb : IsImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R)))` using `MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))).flip hi`. Establish `hc : IsClosedImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R)))` using `IsClosedImmersion.of_isPreimmersion _ hclR`. Rewrite using `[← baseChangeMap_snd]`.

Use `infer_instance`.
-/
theorem exists_fg_isProper_of_isQProjOver (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hp : IsQProjOver p)
    (hV : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨N, i, hi, -, rfl⟩ := hp
  have hq : IsProper (PSpace.str k N) := isProper_str k N

  have hcl : IsClosed (pullback.fst (PSpace.str k N) (spMap (algebraMap k V)) ⁻¹' Set.range i) := by
    rw [← range_baseChangeMap]
    have h1 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V)) ≫
        pullback.snd (PSpace.str k N) (spMap (algebraMap k V))) := by
      rw [baseChangeMap_snd]; exact hV
    have h2 : IsProper (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))) :=
      IsProper.of_comp _ (pullback.snd (PSpace.str k N) (spMap (algebraMap k V)))
    exact (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k V))).isClosedMap.isClosed_range
  obtain ⟨R, hR, hclR⟩ := exists_fg_isClosed_preimage_range k V X (PSpace k N) i (PSpace.str k N) hi inferInstance inferInstance hcl
  refine ⟨R, hR, ?_⟩
  rw [← range_baseChangeMap] at hclR
  have hb : IsImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    MorphismProperty.of_isPullback (P := @IsImmersion)
      (isPullback_baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))).flip hi
  have hc : IsClosedImmersion (baseChangeMap i (PSpace.str k N) (spMap (algebraMap k R))) :=
    IsClosedImmersion.of_isPreimmersion _ hclR
  rw [← baseChangeMap_snd]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
