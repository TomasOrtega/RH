import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieTangent

/- English proof (translation)
Introduce `S G _ R R' _ _ c x E _ _ E' _ _ M M'`. Establish `hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x` using `rfl`. Establish `h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e` using `fun e => M'.onto _ (isTanAt_base c hc (M.tan e))`. Use `choose a ha using h`. Use `⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩` and prove the remaining obligations.

Introduce `e e'`. Apply `M'.inj` to reduce the goal to its premises. Rewrite using `[M'.add, ha, ha, ha, M.add, MonObj.comp_mul]`. Introduce `r e`. Apply `M'.inj` to reduce the goal to its premises.

Rewrite using `[M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]`. Introduce `e`. Express the relevant statement in the definitionally equal form `(M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left`. Rewrite using `[Category.comp_id, ha]`. Both sides reduce to the same expression.

Introduce `j hj`. Use extensionality with `e`. Use `M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `hj e` as an intermediate fact.

Unfold `LieModel.Lifts at this`. Rewrite `this` using `[Category.comp_id]`. Conclude with `this`.
-/
theorem existsUnique_semilinear_lifts :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R')
      (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E']
      (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'),
      ∃! j : E →ₛₗ[c] E', ∀ e, M.Lifts c (𝟙 G.left) e (M'.pt (j e)) := by
  intro S G _ R R' _ _ c x E _ _ E' _ _ M M'
  have hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x := rfl
  have h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base c hc (M.tan e))
  choose a ha using h
  refine ⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro e e'
    apply M'.inj
    rw [M'.add, ha, ha, ha, M.add, MonObj.comp_mul]
  · intro r e
    apply M'.inj
    rw [M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]
  · intro e
    change (M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left
    rw [Category.comp_id, ha]
    rfl
  · intro j hj
    ext e
    refine M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)
    apply Over.OverMorphism.ext
    have := hj e
    unfold LieModel.Lifts at this
    rw [Category.comp_id] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
