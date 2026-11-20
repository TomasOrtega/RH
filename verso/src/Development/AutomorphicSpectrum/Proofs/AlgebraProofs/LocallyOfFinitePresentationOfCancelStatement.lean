import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancel
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LfpDescent.descends` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FLocallyOfFinitePresentationOfCancel.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_cancel : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by
  first | exact @GlobalTheory.CompanionTheory.LfpDescent.descends | exact GlobalTheory.CompanionTheory.LfpDescent.descends | (intros; apply GlobalTheory.CompanionTheory.LfpDescent.descends <;> assumption)
