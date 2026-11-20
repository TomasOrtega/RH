import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ),
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)
