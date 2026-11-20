import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalClosedSubschemesAlgebraiseOpenImmersion.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f → IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion | exact GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion | (intros; apply GlobalTheory.FormalAlg.alg_comp_of_isOpenImmersion <;> assumption)
