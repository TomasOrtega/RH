import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RedTh.balanced_entries_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBalancedEntriesBoundedSiegelReduced.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.balanced_entries_bounded_siegelReduced : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  first | exact @GlobalTheory.RedTh.balanced_entries_bounded | exact GlobalTheory.RedTh.balanced_entries_bounded | (intros; apply GlobalTheory.RedTh.balanced_entries_bounded <;> assumption)
