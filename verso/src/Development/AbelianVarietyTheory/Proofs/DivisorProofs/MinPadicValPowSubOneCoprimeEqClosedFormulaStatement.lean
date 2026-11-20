import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormula
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MinValClosed.mMin_eq_mE` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMinPadicValPowSubOneCoprimeEqClosedFormula.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  first | exact @GlobalTheory.MinValClosed.mMin_eq_mE | exact GlobalTheory.MinValClosed.mMin_eq_mE | (intros; apply GlobalTheory.MinValClosed.mMin_eq_mE <;> assumption)
