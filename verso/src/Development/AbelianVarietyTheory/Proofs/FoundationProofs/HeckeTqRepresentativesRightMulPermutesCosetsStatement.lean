import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqRepresentativesRightMulPermutesCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeTqRepresentativesRightMulPermutesCosets.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets : ∀ (N l q : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → q.Prime → ¬ q ∣ N * l → ∀ σ : SL(2, ℤ), IsDiam N l (q : ZMod N) σ → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin (q + 1)), ∀ i, ∃ γ' : Lev N l, tqFam q σ i * mat γ = mat γ' * tqFam q σ (π i) := by
  first | exact @GlobalTheory.TqPerm.tqFam_perm | exact GlobalTheory.TqPerm.tqFam_perm | (intros; apply GlobalTheory.TqPerm.tqFam_perm <;> assumption)
