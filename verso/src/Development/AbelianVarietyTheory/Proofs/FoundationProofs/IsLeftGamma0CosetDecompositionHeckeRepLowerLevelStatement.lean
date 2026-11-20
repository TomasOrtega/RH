import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.repL_LRep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsLeftGamma0CosetDecompositionHeckeRepLowerLevel.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepLowerLevel : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  first | exact @GlobalTheory.EisM.repL_LRep | exact GlobalTheory.EisM.repL_LRep | (intros; apply GlobalTheory.EisM.repL_LRep <;> assumption)
