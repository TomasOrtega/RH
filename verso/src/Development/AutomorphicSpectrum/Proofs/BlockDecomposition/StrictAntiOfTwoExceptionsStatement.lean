import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptions
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStrictAntiOfTwoExceptions.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.strict_anti_of_two_exceptions : ∀ (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l) (hi : w i = 0) (hj : w j = l - 1) (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a) (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a), StrictAnti w := by
  first | exact @GlobalTheory.CompanionTheory.Segments.shufcomb | exact GlobalTheory.CompanionTheory.Segments.shufcomb | (intros; apply GlobalTheory.CompanionTheory.Segments.shufcomb <;> assumption)
