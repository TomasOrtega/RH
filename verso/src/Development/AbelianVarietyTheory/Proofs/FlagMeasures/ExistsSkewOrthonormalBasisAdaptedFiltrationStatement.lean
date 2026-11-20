import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewOrthonormalBasisAdaptedFiltration
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsSkewOrthonormalBasisAdaptedFiltration.lean&line=204#L204)
-/
theorem _root_.GlobalTheory.T.exists_skew_orthonormal_basis_adapted_filtration : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (deg : Fin d → ℕ), (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ c, Module.finrank ℂ (A c) = Module.finrank ℂ (A (c + 1)) + Fintype.card {i : Fin d // deg i = c}) → ∃ B : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) ∧ (∀ i, Formalism.REAL.inG ε (B i)) ∧ ∀ c, A c = Submodule.span ℂ (B '' {i | c ≤ deg i}) := by
  first | exact @GlobalTheory.SkewBasis.exists_skew_basis | exact GlobalTheory.SkewBasis.exists_skew_basis | (intros; apply GlobalTheory.SkewBasis.exists_skew_basis <;> assumption)
