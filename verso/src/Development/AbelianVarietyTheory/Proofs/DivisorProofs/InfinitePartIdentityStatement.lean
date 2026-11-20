import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuotientNormCoisometry.ipa_tie` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInfinitePartIdentity.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.infinite_part_identity : Bundle → SetAt → InfK → IPa @Comparison₂ := by
  first | exact @GlobalTheory.QuotientNormCoisometry.ipa_tie | exact GlobalTheory.QuotientNormCoisometry.ipa_tie | (intros; apply GlobalTheory.QuotientNormCoisometry.ipa_tie <;> assumption)
