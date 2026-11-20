import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

/- English proof (translation)
Introduce `H S B _ hB g hg k _ _ t n hn`. Establish `hB' : IsAbelianScheme ((Over.pullback t).obj B)` using `{ comm := by have := hB.comm; infer_instance smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance geomConnected := by have := hB.geomConnected; show GeometricallyConnected ( …`. Establish `hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg`. Establish `h` using `H k ((Over.pullback t).obj B) g n hB' hg' hn`. Establish `hp` using `isGrpPullback_pullback B t`.

Establish `hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k))))`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t` using `congrArg (fun z => z.left) hxy`. Conclude with `Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))`.

Introduce `y`. Use `⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (hp.1.lift_fst _ _ _)`. Set `e` to `MulEquiv.ofBijective _ hbij`. Establish `h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ B // x ^ n = 1} = n ^ (2 * g)`.

Rewrite using `[← h]`. Use `(Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations. Use `show x ^ n = 1 ↔ e x ^ n = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`. Establish `h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t` using `Category.id_comp t`.

Rewrite `h2` using `[h3]`. Conclude with `h2`.
-/
theorem card_torsion_geometricPoint_of_field :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (n : ℕ), (n : k) ≠ 0 → Nat.card {x : Over.mk t ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
  intro H S B _ hB g hg k _ _ t n hn
  have hB' : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := H k ((Over.pullback t).obj B) g n hB' hg' hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory
