import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FormalFunctions

/- English proof (translation)
Introduce `A _ _ I hI X hX f hf`. Set `Z : Over (Sp A)` to `Over.mk (𝔸(Unit; Sp A) ↘ Sp A)`. Establish `hZs : IsSeparated Z.hom` using `by dsimp [Z]; infer_instance`. Establish `hZl : LocallyOfFiniteType Z.hom` using `by dsimp [Z]; infer_instance`. Establish `hZq : QuasiCompact Z.hom` using `by dsimp [Z]; infer_instance`.

Set `F : ∀ e, (thickObj A I e X).left ⟶ Z.left` to `fun e => AffineSpace.homOfVector (pullback.fst X.hom (thick A I e) ≫ X.hom) (fun _ => f e)`. Establish `hβ : ∀ e, thickMap A I e X ≫ pullback.fst X.hom (thick A I (e + 1)) = pullback.fst X.hom (thick A I e)`. Introduce `e`. Unfold `thickMap`. Use `first`.

Consider the case `(simp only [pullback.map, pullback.lift_fst, Category.comp_id]; done)`. Consider the case `exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Consider the case `simp [pullback.map]`. Establish `hF₁ : ∀ e, F e ≫ Z.hom = (thickObj A I e X).hom ≫ thick A I e`. Introduce `e`.

Simplify using `[F, Z]`. Rewrite using `[AffineSpace.homOfVector_over]`. Conclude with `pullback.condition`. Establish `hF₂ : ∀ e, thickMap A I e X ≫ F (e + 1) = F e`. Introduce `e`.

Simplify using `[F]`. Rewrite using `[AffineSpace.comp_homOfVector, ← Category.assoc, hβ e]`. Use `congr 1`. Use function extensionality and compare the values at `_`. Conclude with `hf e`.

Take `⟨g, hg, -⟩` from `GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms A I hI X Z hX hZs hZl hZq (fun e => thickObj A I e X) (fun e => thickMap A I e X) (fun e => pullback.fst X.hom (thick A I e)) (fun e => IsPullback.of_hasPullback _ _) hβ F hF₁ hF₂`. Use `⟨g.left.appTop (AffineSpace.coord (Sp A) ()), fun e => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun φ => φ.appTop (AffineSpace.coord (Sp A) ())) (hg e)`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h`. Rewrite using `[h]`.

Conclude with `AffineSpace.homOfVector_appTop_coord _ _ _`.
-/
theorem exists_of_thick : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  intro A _ _ I hI X hX f hf

  let Z : Over (Sp A) := Over.mk (𝔸(Unit; Sp A) ↘ Sp A)
  have hZs : IsSeparated Z.hom := by dsimp [Z]; infer_instance
  have hZl : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  have hZq : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let F : ∀ e, (thickObj A I e X).left ⟶ Z.left := fun e =>
    AffineSpace.homOfVector (pullback.fst X.hom (thick A I e) ≫ X.hom) (fun _ => f e)
  have hβ : ∀ e, thickMap A I e X ≫ pullback.fst X.hom (thick A I (e + 1)) =
      pullback.fst X.hom (thick A I e) := by
    intro e
    unfold thickMap
    first
      | (simp only [pullback.map, pullback.lift_fst, Category.comp_id]; done)
      | exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      | simp [pullback.map]
  have hF₁ : ∀ e, F e ≫ Z.hom = (thickObj A I e X).hom ≫ thick A I e := by
    intro e
    dsimp [F, Z]
    rw [AffineSpace.homOfVector_over]
    exact pullback.condition
  have hF₂ : ∀ e, thickMap A I e X ≫ F (e + 1) = F e := by
    intro e
    dsimp [F]
    rw [AffineSpace.comp_homOfVector, ← Category.assoc, hβ e]
    congr 1
    funext _
    exact hf e
  obtain ⟨g, hg, -⟩ := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms A I hI X Z hX hZs hZl hZq
    (fun e => thickObj A I e X) (fun e => thickMap A I e X) (fun e => pullback.fst X.hom (thick A I e))
    (fun e => IsPullback.of_hasPullback _ _) hβ F hF₁ hF₂
  refine ⟨g.left.appTop (AffineSpace.coord (Sp A) ()), fun e => ?_⟩
  have h := congrArg (fun φ => φ.appTop (AffineSpace.coord (Sp A) ())) (hg e)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  rw [h]
  exact AffineSpace.homOfVector_appTop_coord _ _ _

end GlobalTheory.FormalFunctions
