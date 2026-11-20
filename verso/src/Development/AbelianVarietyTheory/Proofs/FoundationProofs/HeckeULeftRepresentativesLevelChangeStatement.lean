import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeULeftRepresentativesLevelChange
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeULeftRepresentativesLevelChange.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.heckeU_leftRepresentatives_level_change : ∀ L l : ℕ, l.Prime → (l ∣ L → LRep L (DU L l) (repU l)) ∧ (l ∣ L → LRep (L * l) {δ | δ ∈ DU L l ∧ ((L * l : ℕ) : ℤ) ∣ δ 1 0} (repU l)) := by
  first | exact @GlobalTheory.EisM.zrepU | exact GlobalTheory.EisM.zrepU | (intros; apply GlobalTheory.EisM.zrepU <;> assumption)
