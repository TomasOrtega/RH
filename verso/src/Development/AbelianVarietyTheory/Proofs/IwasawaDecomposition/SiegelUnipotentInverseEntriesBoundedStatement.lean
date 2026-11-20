import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelUnipotentInverseEntriesBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSiegelUnipotentInverseEntriesBounded.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.siegelUnipotent_inverse_entries_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  first | exact @GlobalTheory.siegel_unipotent_inv_bounded | exact GlobalTheory.siegel_unipotent_inv_bounded | (intros; apply GlobalTheory.siegel_unipotent_inv_bounded <;> assumption)
