import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTraceBoundedOfAevalMonicEqZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero : ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ, Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  first | exact @GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | exact GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | (intros; apply GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero <;> assumption)
