import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityAbelianScheme
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_abelianScheme : GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.poincareDeRhamDuality | exact GlobalTheory.poincareDeRhamDuality | (intros; apply GlobalTheory.poincareDeRhamDuality <;> assumption)
