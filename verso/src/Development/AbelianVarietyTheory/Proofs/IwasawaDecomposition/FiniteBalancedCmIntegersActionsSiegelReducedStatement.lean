import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBalancedCmIntegersActionsSiegelReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFiniteBalancedCmIntegersActionsSiegelReduced.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_balanced_cmIntegers_actions_siegelReduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  first | exact @GlobalTheory.RedTh.finite_balanced_actions | exact GlobalTheory.RedTh.finite_balanced_actions | (intros; apply GlobalTheory.RedTh.finite_balanced_actions <;> assumption)
