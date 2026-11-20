import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianDeRhamPoincareDualityOfCubeDual.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  first | exact @GlobalTheory.CubeDual.abelianDeRham_duality | exact GlobalTheory.CubeDual.abelianDeRham_duality | (intros; apply GlobalTheory.CubeDual.abelianDeRham_duality <;> assumption)
