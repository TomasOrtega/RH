import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

/- English proof (translation)
Introduce `R _ _ A F _ _ _ em N hN x hx`. Take `⟨K', _, _, hfin, H⟩` from `TorsRational.exists_ext_points (FractionRing R) (torsion A.A N) (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1`. Set `i : K' →ₐ[FractionRing R] Kb R` to `IsAlgClosed.lift`. Set `: Algebra K' (Kb R)` to `i.toRingHom.toAlgebra`. Establish `: IsScalarTower (FractionRing R) K' (Kb R)` using `IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm`.

Establish `hmul : x ≫ mulN A.A N = toUnit _ ≫ η`. Rewrite using `[GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]`. Set `t0 : _ ⟶ torsion A.A N` to `pullback.lift x (toUnit _) hmul`. Establish `ht0 : t0 ≫ torsion.ι A.A N = x` using `pullback.lift_fst _ _ _`. Establish `hs : (TFK (R` using `R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) := congrArg spMap em.comp_algebraMap.symm`.

Take `⟨w, hw⟩` from `H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)`. Establish `hw2 : w ≫ (torsion A.A N).hom = (TFK (R` using `R) (Kb R)).hom := by`. Use `spec_map_field_cancel em.toRingHom _ _ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]`. Both sides reduce to the same expression.

Set `w1 : TFK (R` to `R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2`. Use `⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η` using `pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))`. Establish `h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η`. Rewrite using `[Category.assoc, hc, ← Category.assoc, comp_toUnit]`.

Rewrite `h1` using `[GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def]`. Then use the resulting hypothesis. Rewrite using `[← ht0, Over.comp_left, ← hw, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := IsAlgClosed.lift
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    refine spec_map_field_cancel em.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
