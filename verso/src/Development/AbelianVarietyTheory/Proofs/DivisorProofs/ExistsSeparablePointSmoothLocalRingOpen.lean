import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ U hU O hO`. Take `⟨W, _, _, _, ε, y, hy, hyO⟩` from `GlobalTheory.exists_etale_point_of_smooth U.hom R (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)`. Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)`. Set `k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R))` to `IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))`. Establish `hfin : FiniteDimensional (ResidueField R) k'` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`.

Establish `hsep : Algebra.IsSeparable (ResidueField R) k'` using `Algebra.IsSeparable.of_algHom _ _ k'.val`. Establish `hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε` using `Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩`. Establish `hmem : ∀ w, ε w ∈ k'` using `fun w => hle (hs ▸ Algebra.mem_top)`. Set `g : W →+* k'` to `ε.toRingHom.codRestrict k' hmem`. Use `⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hy, Category.comp_id, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `r`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)`. Rewrite using `[ε.commutes]`. Conclude with `IsScalarTower.algebraMap_apply R (ResidueField R) _ r`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hyO ⟨_, rfl⟩`.
-/
theorem exists_separable_point_of_smooth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom →
    ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k')
      (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left),
      x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  intro R _ _ U hU O hO
  obtain ⟨W, _, _, _, ε, y, hy, hyO⟩ := GlobalTheory.exists_etale_point_of_smooth U.hom R
    (SeparableClosure (ResidueField R)) (𝟙 _) O (by obtain ⟨u, hu, e⟩ := hO; exact ⟨u, hu, e⟩)
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R W).FG)
  let k' : IntermediateField (ResidueField R) (SeparableClosure (ResidueField R)) :=
    IntermediateField.adjoin (ResidueField R) (ε '' (s : Set W))
  have hfin : FiniteDimensional (ResidueField R) k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsep : Algebra.IsSeparable (ResidueField R) k' := Algebra.IsSeparable.of_algHom _ _ k'.val
  have hle : Algebra.adjoin R (s : Set W) ≤ (k'.toSubalgebra.restrictScalars R).comap ε :=
    Algebra.adjoin_le fun w hw => IntermediateField.subset_adjoin _ _ ⟨w, hw, rfl⟩
  have hmem : ∀ w, ε w ∈ k' := fun w => hle (hs ▸ Algebra.mem_top)
  let g : W →+* k' := ε.toRingHom.codRestrict k' hmem
  refine ⟨k', inferInstance, inferInstance, hfin, hsep, Spec.map (CommRingCat.ofHom g) ≫ y, ?_, ?_⟩
  · rw [Category.assoc, hy, Category.comp_id, ← Spec.map_comp]
    congr 2
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    change ε (algebraMap R W r) = algebraMap (ResidueField R) _ (residue R r)
    rw [ε.commutes]
    exact IsScalarTower.algebraMap_apply R (ResidueField R) _ r
  · rintro _ ⟨z, rfl⟩
    exact hyO ⟨_, rfl⟩

end GlobalTheory.Mum
