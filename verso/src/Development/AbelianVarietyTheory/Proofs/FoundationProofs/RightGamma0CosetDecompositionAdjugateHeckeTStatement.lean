import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightGamma0CosetDecompositionAdjugateHeckeT
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.rrep_DT_adj_repT` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FRightGamma0CosetDecompositionAdjugateHeckeT.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  first | exact @GlobalTheory.EisM.rrep_DT_adj_repT | exact GlobalTheory.EisM.rrep_DT_adj_repT | (intros; apply GlobalTheory.EisM.rrep_DT_adj_repT <;> assumption)
