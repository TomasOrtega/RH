import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHermitianSqrtInSignedUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsHermitianSqrtInSignedUnitaryGroup.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ), C.det ≠ 0 → (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε → ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  first | exact @GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | exact GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ | (intros; apply GlobalTheory.LeviIso.exists_hermitian_sqrt_mem_UJ <;> assumption)
