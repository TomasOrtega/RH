import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientSeparationOfHarishChandra
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepPseudo.pseudoCoeffSeparation` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPseudocoefficientSeparationOfHarishChandra.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.pseudocoefficient_separation_of_harish_chandra : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  first | exact @GlobalTheory.SepPseudo.pseudoCoeffSeparation | exact GlobalTheory.SepPseudo.pseudoCoeffSeparation | (intros; apply GlobalTheory.SepPseudo.pseudoCoeffSeparation <;> assumption)
