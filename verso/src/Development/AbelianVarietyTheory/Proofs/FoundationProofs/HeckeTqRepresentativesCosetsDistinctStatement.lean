import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesCosetsDistinct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.tqFam_cosets_distinct` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeTqRepresentativesCosetsDistinct.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.heckeTqRepresentatives_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime → tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  first | exact @GlobalTheory.tqFam_cosets_distinct | exact GlobalTheory.tqFam_cosets_distinct | (intros; apply GlobalTheory.tqFam_cosets_distinct <;> assumption)
