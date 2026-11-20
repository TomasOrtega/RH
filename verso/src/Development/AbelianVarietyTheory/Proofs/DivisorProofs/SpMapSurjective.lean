import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bcMap_hom {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom = (Over.pullback (spMap (algebraMap K L))).map f.hom := rfl

instance spMap_surjective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] :
    Surjective (spMap (algebraMap K L)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Rewrite using `[bcMap_hom]`. Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem bcMap_left_fst {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom.left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left := by
  rw [bcMap_hom]
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Introduce `f g h`. Establish `: Epi (pullback.fst A.X.hom (spMap (algebraMap K L)))` using `Flat.epi_of_flat_of_surjective _`. Apply `hom_ext` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_epi (pullback.fst A.X.hom (spMap (algebraMap K L))), ← bcMap_left_fst, ← bcMap_left_fst, h]`.
-/
theorem bcMap_injective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) :
    Function.Injective (bcMap L : (A ⟶ B) → _) := by
  intro f g h
  have : Epi (pullback.fst A.X.hom (spMap (algebraMap K L))) := Flat.epi_of_flat_of_surjective _
  apply hom_ext
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst A.X.hom (spMap (algebraMap K L))), ← bcMap_left_fst, ← bcMap_left_fst, h]

/- English proof (translation)
The claim follows from `hom_ext (Functor.map_mul (Over.pullback (spMap (algebraMap K L))) f.hom g.hom)`.
-/
theorem bcMap_add {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f g : A ⟶ B) :
    bcMap L (f + g) = bcMap L f + bcMap L g :=
  hom_ext (Functor.map_mul (Over.pullback (spMap (algebraMap K L))) f.hom g.hom)

/- English proof (translation)
The claim follows from `hom_ext ((Over.pullback (spMap (algebraMap K L))).map_comp f.hom g.hom)`.
-/
theorem bcMap_comp {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B C : AbVar K} (f : A ⟶ B)
    (g : B ⟶ C) : bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g :=
  hom_ext ((Over.pullback (spMap (algebraMap K L))).map_comp f.hom g.hom)

/- English proof (translation)
The claim follows from `hom_ext ((Over.pullback (spMap (algebraMap K L))).map_id A.X)`.
-/
theorem bcMap_id {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) :
    bcMap L (𝟙 A) = 𝟙 _ :=
  hom_ext ((Over.pullback (spMap (algebraMap K L))).map_id A.X)

/- English proof (translation)
Introduce `_ _ L _ _ A B _` and use `⟨bcMap_add L, bcMap_comp L, bcMap_id L A, bcMap_injective L A B⟩`.
-/
theorem bcMap_functorial : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B C : AbVar K),
    (∀ f g : A ⟶ B, bcMap L (f + g) = bcMap L f + bcMap L g) ∧
    (∀ (f : A ⟶ B) (g : B ⟶ C), bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g) ∧ bcMap L (𝟙 A) = 𝟙 _ ∧
    Function.Injective (bcMap L : (A ⟶ B) → _) :=
  fun _ _ L _ _ A B _ => ⟨bcMap_add L, bcMap_comp L, bcMap_id L A, bcMap_injective L A B⟩

end GlobalTheory.AV.AbVar

end
