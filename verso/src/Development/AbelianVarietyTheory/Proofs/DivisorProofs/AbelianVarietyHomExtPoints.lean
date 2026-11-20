import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A B f g h`. Use `A.ab.smooth` as an intermediate fact. Use `B.ab.proper` as an intermediate fact. Establish `: IsReduced A.X.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom`. Set `Ω` to `AlgebraicClosure K`.

Set `q : Sp Ω ⟶ Sp K` to `spMap (algebraMap K Ω)`. Establish `: Surjective q` using `⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩`. Establish `: JacobsonSpace ↥(pullback A.X.hom q)` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)`. Establish `hd : Dense (closedPoints ↥(pullback A.X.hom q))` using `dense_iff_closure_eq.2 closure_closedPoints`. Establish `hD` using `(pullback.fst A.X.hom q).surjective.denseRange.dense_image (pullback.fst A.X.hom q).continuous hd`.

Establish `hdom : IsDominant (equalizer.ι f.hom.left g.hom.left)`. Use `⟨hD.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw₀, rfl⟩`. Establish `hw : IsClosed ({w} : Set ↥(pullback A.X.hom q))` using `hw₀`. Set `y : Sp Ω ⟶ A.X.left` to `pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q`.

Establish `hy : y ≫ A.X.hom = q`. Simplify using `only [y, Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]`. Set `x : A.Pt` to `Over.homMk y hy`. Establish `hx : y ≫ f.hom.left = y ≫ g.hom.left` using `congrArg CommaMorphism.left (h x)`.

Use `⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _`. Rewrite using `[equalizer.lift_ι]`. Conclude with `congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)`. Conclude with `hom_ext (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _)))`.
-/
theorem ext_of_pt_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f g : A ⟶ B),
    (∀ x : A.Pt, x ≫ f.hom = x ≫ g.hom) → f = g := by
  intro K _ A B f g h
  have := A.ab.smooth
  have := B.ab.proper
  have : IsReduced A.X.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback A.X.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)
  have hd : Dense (closedPoints ↥(pullback A.X.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst A.X.hom q).surjective.denseRange.dense_image
    (pullback.fst A.X.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι f.hom.left g.hom.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback A.X.hom q)) := hw₀
    let y : Sp Ω ⟶ A.X.left :=
      pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q
    have hy : y ≫ A.X.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : A.Pt := Over.homMk y hy
    have hx : y ≫ f.hom.left = y ≫ g.hom.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)
  exact hom_ext (Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _)))

end GlobalTheory.AV.AbVar
