import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDefinitionFromAnchor
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowDefinitionFromAnchor.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.low_definition_from_anchor : Hypotheses2 → Gram → Anchor → LowDef := by
  first | exact @GlobalTheory.CovTop.DefLow.lowDef | exact GlobalTheory.CovTop.DefLow.lowDef | (intros; apply GlobalTheory.CovTop.DefLow.lowDef <;> assumption)
