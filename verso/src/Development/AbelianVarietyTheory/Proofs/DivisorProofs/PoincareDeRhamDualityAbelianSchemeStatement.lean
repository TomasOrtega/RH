import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.poincareDeRhamDuality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPoincareDeRhamDualityAbelianScheme.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_abelianScheme : GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)
