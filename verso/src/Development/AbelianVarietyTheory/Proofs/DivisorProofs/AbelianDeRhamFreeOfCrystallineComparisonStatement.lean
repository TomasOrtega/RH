import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.abelianDeRhamFree_of_hodge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianDeRhamFreeOfCrystallineComparison.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  first | exact @GlobalTheory.Proof.abelianDeRhamFree_of_hodge | exact GlobalTheory.Proof.abelianDeRhamFree_of_hodge | (intros; apply GlobalTheory.Proof.abelianDeRhamFree_of_hodge <;> assumption)
