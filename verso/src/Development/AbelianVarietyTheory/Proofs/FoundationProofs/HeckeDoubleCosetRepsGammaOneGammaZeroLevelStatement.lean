import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeDoubleCosetRepsGammaOneGammaZeroLevel.lean&line=395#L395)
-/
theorem _root_.GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ → IsDCReps (Lev N l) (dg 1 q) (tqFam q σ)) ∧ IsDCReps (Lev N l) (dg 1 l) (ulFam l) ∧ ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → IsDCReps (Lev N l) (mat σ) (fun _ : Unit => mat σ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level | exact GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level | (intros; apply GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level <;> assumption)
