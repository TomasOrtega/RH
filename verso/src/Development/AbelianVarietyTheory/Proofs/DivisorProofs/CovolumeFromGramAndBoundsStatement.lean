import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.Assembly.covolX_of_steps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCovolumeFromGramAndBounds.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.covolume_from_gram_and_bounds : Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  first | exact @GlobalTheory.CovTop.Assembly.covolX_of_steps | exact GlobalTheory.CovTop.Assembly.covolX_of_steps | (intros; apply GlobalTheory.CovTop.Assembly.covolX_of_steps <;> assumption)
