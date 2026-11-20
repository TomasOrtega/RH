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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
