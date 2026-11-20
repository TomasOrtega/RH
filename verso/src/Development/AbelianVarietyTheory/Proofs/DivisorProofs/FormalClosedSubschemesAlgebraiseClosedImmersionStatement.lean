import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalAlg.alg_of_isClosedImmersion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalClosedSubschemesAlgebraiseClosedImmersion.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I → Alg (i ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isClosedImmersion | exact GlobalTheory.FormalAlg.alg_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.alg_of_isClosedImmersion <;> assumption)
