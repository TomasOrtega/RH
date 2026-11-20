import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

/- English proof (translation)
Use `⟨?_, fun c => ?_⟩` and prove the remaining obligations. Unfold `formPoly`. Use `IsHomogeneous.sum _ _ _ fun w _ => ?_` and prove the remaining obligations. Establish `h : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous (∑ _j : Fin n, 1)` using `IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _`. Establish `h' : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous n` using `by simpa using h`.

Conclude with `h'.C_mul _`. Simplify using `[formPoly, map_sum, map_prod]`.
-/
theorem formPoly_isHomogeneous_and_eval (σ : Type) [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) :
    (formPoly n a).IsHomogeneous n ∧
      ∀ c : σ → ℝ, eval c (formPoly n a) = ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
  classical
  refine ⟨?_, fun c => ?_⟩
  · unfold formPoly
    refine IsHomogeneous.sum _ _ _ fun w _ => ?_
    have h : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous (∑ _j : Fin n, 1) :=
      IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _
    have h' : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous n := by simpa using h
    exact h'.C_mul _
  · simp [formPoly, map_sum, map_prod]

end GlobalTheory.CompanionTheory.Ar.PB
