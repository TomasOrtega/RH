import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeStatementHolds.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.lattice_statement_holds : LatSt := by
  first | exact @GlobalTheory.FlatModel.LatDual.latSt | exact GlobalTheory.FlatModel.LatDual.latSt | (intros; apply GlobalTheory.FlatModel.LatDual.latSt <;> assumption)
