import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCommFormalGroupLawOfIsLawOf.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  first | exact @GlobalTheory.Katz.Chart.isLaw_of_isLawOf | exact GlobalTheory.Katz.Chart.isLaw_of_isLawOf | (intros; apply GlobalTheory.Katz.Chart.isLaw_of_isLawOf <;> assumption)
