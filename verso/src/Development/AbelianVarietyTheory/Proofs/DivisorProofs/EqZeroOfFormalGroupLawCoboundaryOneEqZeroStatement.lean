import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.eq_zero_of_cob1_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEqZeroOfFormalGroupLawCoboundaryOneEqZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ) (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  first | exact @GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | exact GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.Katz.eq_zero_of_cob1_eq_zero <;> assumption)
