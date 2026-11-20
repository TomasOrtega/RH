import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsRelevantBruhatCellsLevelDatum.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  first | exact @GlobalTheory.BadShare.Cells.relevant_cells | exact GlobalTheory.BadShare.Cells.relevant_cells | (intros; apply GlobalTheory.BadShare.Cells.relevant_cells <;> assumption)
