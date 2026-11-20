import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClosedLev.isClosedImmersion_of_mod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsClosedImmersionOfProperClosedImmersionModIdeal.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.isClosedImmersion_of_proper_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.ClosedLev.isClosedImmersion_of_mod | exact GlobalTheory.ClosedLev.isClosedImmersion_of_mod | (intros; apply GlobalTheory.ClosedLev.isClosedImmersion_of_mod <;> assumption)
