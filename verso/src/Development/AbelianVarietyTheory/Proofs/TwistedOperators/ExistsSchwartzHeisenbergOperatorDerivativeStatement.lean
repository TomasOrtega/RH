import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsSchwartzHeisenbergOperatorDerivative.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ),
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)
