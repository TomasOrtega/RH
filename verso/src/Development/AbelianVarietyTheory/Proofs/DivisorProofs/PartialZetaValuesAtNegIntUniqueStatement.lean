import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUnique
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZetaValUnique.classZetaVals_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPartialZetaValuesAtNegIntUnique.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.partialZeta_values_at_neg_int_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k → ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  first | exact @GlobalTheory.ZetaValUnique.classZetaVals_unique | exact GlobalTheory.ZetaValUnique.classZetaVals_unique | (intros; apply GlobalTheory.ZetaValUnique.classZetaVals_unique <;> assumption)
