import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicMemFiniteDimensionalCompactStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FockAlg.fin_harm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockHarmonicMemFiniteDimensionalCompactStable.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.fockHarmonic_mem_finiteDimensional_compactStable : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S → ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧ (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧ KStable (fockAct2 P Q R S) H0 := by
  first | exact @GlobalTheory.FockAlg.fin_harm | exact GlobalTheory.FockAlg.fin_harm | (intros; apply GlobalTheory.FockAlg.fin_harm <;> assumption)
