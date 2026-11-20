import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepSchwartzPolynomialBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerRepSchwartzPolynomialBound.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n), Continuous G ∧
    (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N := by
  first | exact @GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | exact GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | (intros; apply GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun <;> assumption)
