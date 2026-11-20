import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `R S B C _ _ _ _ _ _ _ a h`. Take `⟨φ, rfl⟩` from `Spec.map_surjective (R := CommRingCat.of B) (S := CommRingCat.of C) a`. Establish `h1 : IsPullback φ.op (CommRingCat.ofHom (algebraMap S C)).op (CommRingCat.ofHom (algebraMap R B)).op (CommRingCat.ofHom (algebraMap R S)).op` using `IsPullback.of_map_of_faithful Scheme.Spec h`. Establish `h2 : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom (algebraMap S C)) φ` using `h1.unop`. Use `letI : Algebra B C := φ.hom.toAlgebra`.

Use `letI : Algebra R C := ((algebraMap S C).comp (algebraMap R S)).toAlgebra`. Use `haveI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h2.w)`. Use `haveI : Algebra.IsPushout R S B C := CommRingCat.isPushout_iff_isPushout.mp h2`. Conclude with `⟨Algebra.IsPushout.equiv R S B C⟩`.
-/
theorem tensorProduct_algEquiv_of_isPullback_spec : ∀ (R S B C : Type) [CommRing R] [CommRing S] [CommRing B] [CommRing C] [Algebra R S] [Algebra R B] [Algebra S C] (a : Sp C ⟶ Sp B), IsPullback a (spMap (algebraMap S C)) (spMap (algebraMap R B)) (spMap (algebraMap R S)) → Nonempty ((S ⊗[R] B) ≃ₐ[S] C) := by
  intro R S B C _ _ _ _ _ _ _ a h
  obtain ⟨φ, rfl⟩ := Spec.map_surjective (R := CommRingCat.of B) (S := CommRingCat.of C) a
  have h1 : IsPullback φ.op (CommRingCat.ofHom (algebraMap S C)).op
      (CommRingCat.ofHom (algebraMap R B)).op (CommRingCat.ofHom (algebraMap R S)).op :=
    IsPullback.of_map_of_faithful Scheme.Spec h
  have h2 : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap S C)) φ := h1.unop
  letI : Algebra B C := φ.hom.toAlgebra
  letI : Algebra R C := ((algebraMap S C).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h2.w)
  haveI : Algebra.IsPushout R S B C := CommRingCat.isPushout_iff_isPushout.mp h2
  exact ⟨Algebra.IsPushout.equiv R S B C⟩
end GlobalTheory
