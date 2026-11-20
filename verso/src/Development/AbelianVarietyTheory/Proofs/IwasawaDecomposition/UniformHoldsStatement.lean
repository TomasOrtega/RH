import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.Unif.uniformSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUniformHolds.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.uniform_holds : UniformSt := by
  first | exact @GlobalTheory.TorRef.Unif.uniformSt | exact GlobalTheory.TorRef.Unif.uniformSt | (intros; apply GlobalTheory.TorRef.Unif.uniformSt <;> assumption)
