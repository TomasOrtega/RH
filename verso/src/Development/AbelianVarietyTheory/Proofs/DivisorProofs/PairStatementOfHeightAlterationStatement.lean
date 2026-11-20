import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairStatementOfHeightAlteration
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration

/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPairStatementOfHeightAlteration.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.pair_statement_of_height_alteration : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.PairTerm.PairSt := by
  first | exact @GlobalTheory.PairTerm.pairSt | exact GlobalTheory.PairTerm.pairSt | (intros; apply GlobalTheory.PairTerm.pairSt <;> assumption)
