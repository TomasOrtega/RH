import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalAlg.hom_eq_of_reductions_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMorphismEqOfEqOnThickenings.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.morphism_eq_of_eq_on_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | exact GlobalTheory.FormalAlg.hom_eq_of_reductions_eq | (intros; apply GlobalTheory.FormalAlg.hom_eq_of_reductions_eq <;> assumption)
