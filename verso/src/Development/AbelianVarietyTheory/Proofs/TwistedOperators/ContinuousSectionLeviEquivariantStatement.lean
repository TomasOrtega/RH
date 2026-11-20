import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousSectionLeviEquivariant
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FContinuousSectionLeviEquivariant.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.continuous_section_levi_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V, Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  first | exact @GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero | exact GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero | (intros; apply GlobalTheory.RealInd.exists_kLevi_equivariant_ne_zero <;> assumption)
