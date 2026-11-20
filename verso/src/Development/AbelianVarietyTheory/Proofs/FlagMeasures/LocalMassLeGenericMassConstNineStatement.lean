import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.localMass_le_genericMass_nine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalMassLeGenericMassConstNine.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.localMass_le_genericMass_const_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  first | exact @GlobalTheory.localMass_le_genericMass_nine | exact GlobalTheory.localMass_le_genericMass_nine | (intros; apply GlobalTheory.localMass_le_genericMass_nine <;> assumption)
