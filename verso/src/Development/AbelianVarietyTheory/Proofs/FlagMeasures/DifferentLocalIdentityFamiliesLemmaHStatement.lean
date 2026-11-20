import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTieLeaf.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDifferentLocalIdentityFamiliesLemmaH.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.differentLocalIdentity_familiesLemmaH : Formalism.L2.SG.FamDefs.HTie := by
  first | exact @GlobalTheory.HTieLeaf.main | exact GlobalTheory.HTieLeaf.main | (intros; apply GlobalTheory.HTieLeaf.main <;> assumption)
