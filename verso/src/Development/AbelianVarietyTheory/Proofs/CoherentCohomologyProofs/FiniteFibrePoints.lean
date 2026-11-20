import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosedStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbTorsionFinite

/- English proof (translation)
Establish `hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite` using `f.left.finite_preimage_singleton _`. Use `hfin.to_subtype` as an intermediate fact. Use `Finite.of_injective (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by` and prove the remaining obligations. Establish `h` using `congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2`. Conclude with `h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_`.

Introduce `a b hab`. Use `Subtype.ext (Over.OverMorphism.ext ?_)` and prove the remaining obligations. Conclude with `ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1) (congrArg Subtype.val hab)`.
-/
theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

/- English proof (translation)
Introduce `K _ _ B _ hB n hn`. Use `GlobalTheory.T.isFinite_mulByNat_abelianVariety_algClosed K B hB n hn` as an intermediate fact. Establish `: IsProper B.hom` using `hB.proper`. Use `finite_fibre_points (mulA B n) 1` as an intermediate fact. Use `Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulA B n = 1) fun x => ?_)` and prove the remaining obligations.

Establish `: x ≫ mulA B n = x ^ n`. Rewrite using `[mulA, MonObj.comp_pow, Category.comp_id]`. Rewrite using `[this]`.
-/
theorem finite_torsion : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B // x ^ n = 1} := by
  intro K _ _ B _ hB n hn
  have := GlobalTheory.T.isFinite_mulByNat_abelianVariety_algClosed K B hB n hn
  have : IsProper B.hom := hB.proper
  have := finite_fibre_points (mulA B n) 1
  refine Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulA B n = 1) fun x => ?_)
  have : x ≫ mulA B n = x ^ n := by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  rw [this]

end GlobalTheory.AbTorsionFinite
