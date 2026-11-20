import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUniquenessOfCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
open GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeUniquenessOfCovering.lean&line=334#L334)
-/
theorem _root_.GlobalTheory.T.lattice_uniqueness_of_covering : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.ChainPts.LatUniqueSt := by
  first | exact @GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems | exact GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems | (intros; apply GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems <;> assumption)
