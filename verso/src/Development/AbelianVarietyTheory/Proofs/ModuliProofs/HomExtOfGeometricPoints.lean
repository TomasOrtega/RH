import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

/- English proof (translation)
Establish `hs : Surjective (equalizer.ι f g)` using `⟨fun s => by`. Set `k` to `AlgebraicClosure (S.residueField s)`. Set `x : Sp k ⟶ S` to `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) ≫ S.fromSpecResidueField s`. Establish `hx` using `h k x`. Set `p : Sp k` to `IsLocalRing.closedPoint k`.

Use `⟨equalizer.lift x hx p, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, equalizer.lift_ι]`. Simplify using `only [x, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _⟩`. Conclude with `ext_of_isDominant_of_isSeparated q hq (equalizer.ι f g) (equalizer.condition _ _)`.
-/
theorem hom_ext_of_geometric_points (S X Z : Scheme.{0}) [IsReduced S] (q : X ⟶ Z)
    [IsSeparated q] (f g : S ⟶ X) (hq : f ≫ q = g ≫ q)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), x ≫ f = x ≫ g) : f = g := by
  have hs : Surjective (equalizer.ι f g) := ⟨fun s => by
    let k := AlgebraicClosure (S.residueField s)
    let x : Sp k ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) ≫ S.fromSpecResidueField s
    have hx := h k x
    let p : Sp k := IsLocalRing.closedPoint k
    refine ⟨equalizer.lift x hx p, ?_⟩
    rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _⟩
  exact ext_of_isDominant_of_isSeparated q hq (equalizer.ι f g) (equalizer.condition _ _)

end GlobalTheory.HkFam
