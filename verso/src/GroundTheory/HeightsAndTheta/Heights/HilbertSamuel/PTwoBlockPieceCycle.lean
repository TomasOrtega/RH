import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceIndex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsModulePieceHilbert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem TwoBlockPieceCycle.proof (hA : TwoBlockPieceIndex.Statement) (hF : TwoBlockModuleFinite.Statement)
    (hH : ModulePieceHilbert.Statement) (hC : TwoBlockModuleCycle.Statement) : TwoBlockPieceCycle.Statement := by
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl
  obtain ⟨hm₁, hm₂, hle, ⟨N, hN, hNJ⟩, hdim⟩ := hF D Ω κ x B c l hX hx hB hsp hl
  obtain ⟨a₀, C, h⟩ := hH (Fin 2) (FinTwoTypeFamily κ) _ _ N D hm₁ hm₂ hle hN hNJ hdim (fun _ => 1)
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  have h1 := h ![a, b] (fun k => by fin_cases k <;> simpa)
  have e1 : (![a, b] + fun _ => 1 : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun (_ : Fin D) (k : Fin 2) => ((![a, b] k : ℕ) : ℤ)) = fun _ => ![(a : ℤ), (b : ℤ)] := by
    funext _ k
    fin_cases k <;> rfl
  have e3 : ((∑ k, ![a, b] k : ℕ) : ℝ) = (a + b : ℝ) := by
    simp [Fin.sum_univ_two]
  rw [e1, e2, hC D Ω κ x B c l hX hx hB hsp hl, e3] at h1
  rw [hA D Ω κ x B c l hX hx hB hsp hl a b]
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
