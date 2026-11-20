import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDvdOfRingOfIntegersToIntMatrix
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankDvdOfRingOfIntegersToIntMatrix.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.finrank_dvd_of_ringOfIntegers_to_int_matrix : ∀ (E : Type) [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  first | exact @GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | exact GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix | (intros; apply GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix <;> assumption)
