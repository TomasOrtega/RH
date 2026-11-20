import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FReAntidiagonalEntryEqZeroOfFlagDepth.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.re_corner_eq_zero | exact GlobalTheory.SnMass.VolN.re_corner_eq_zero | (intros; apply GlobalTheory.SnMass.VolN.re_corner_eq_zero <;> assumption)
