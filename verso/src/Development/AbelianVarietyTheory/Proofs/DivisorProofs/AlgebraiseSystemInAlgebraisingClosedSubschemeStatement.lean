import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraiseSystemInAlgebraisingClosedSubscheme.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) → ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  first | exact @GlobalTheory.FormalAlg.alg_of_closedSubscheme | exact GlobalTheory.FormalAlg.alg_of_closedSubscheme | (intros; apply GlobalTheory.FormalAlg.alg_of_closedSubscheme <;> assumption)
