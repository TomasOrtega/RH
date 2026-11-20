import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.abelianDeRham_of_duality` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianDeRhamOfDuality.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.abelian_de_rham_of_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.AbelianDeRhamStructure → GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_duality | exact GlobalTheory.abelianDeRham_of_duality | (intros; apply GlobalTheory.abelianDeRham_of_duality <;> assumption)
