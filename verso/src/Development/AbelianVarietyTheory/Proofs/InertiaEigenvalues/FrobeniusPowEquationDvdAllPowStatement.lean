import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPow
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.phiEq_dvd_all_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusPowEquationDvdAllPow.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.frobeniusPowEquation_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.phiEq_dvd_all_pow | exact GlobalTheory.phiEq_dvd_all_pow | (intros; apply GlobalTheory.phiEq_dvd_all_pow <;> assumption)
