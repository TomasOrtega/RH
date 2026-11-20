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
Introduce `D Ω _ _ κ _ x B c l hX hx hB hsp hl`. Take `⟨hm₁, hm₂, hle, ⟨N, hN, hNJ⟩, hdim⟩` from `hF D Ω κ x B c l hX hx hB hsp hl`. Take `⟨a₀, C, h⟩` from `hH (Fin 2) (FinTwoTypeFamily κ) _ _ N D hm₁ hm₂ hle hN hNJ hdim (fun _ => 1)`. Use `⟨a₀, C, fun a b ha hb => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have h1 := h ![a, b] (fun k => by fin_cases k <;> simpa)`.

Establish `e1 : (![a, b] + fun _ => 1 : Fin 2 → ℕ) = ![a + 1, b + 1]`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `fin_cases k <;> rfl`. Establish `e2 : (fun (_ : Fin D) (k : Fin 2) => ((![a, b] k : ℕ) : ℤ)) = fun _ => ![(a : ℤ), (b : ℤ)]`. Use function extensionality and compare the values at `_ k`.

Apply the tactic sequence `fin_cases k <;> rfl`. Establish `e3 : ((∑ k, ![a, b] k : ℕ) : ℝ) = (a + b : ℝ)`. Simplify using `[Fin.sum_univ_two]`. Rewrite `h1` using `[e1, e2, hC D Ω κ x B c l hX hx hB hsp hl, e3]`. Rewrite using `[hA D Ω κ x B c l hX hx hB hsp hl a b]`.

Conclude with `h1`.
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
