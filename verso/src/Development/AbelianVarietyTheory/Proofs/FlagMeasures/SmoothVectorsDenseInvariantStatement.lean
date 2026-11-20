import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSmoothVectorsDenseInvariant.lean&line=209#L209)
-/
theorem _root_.GlobalTheory.T.smooth_vectors_dense_invariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ → (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧ (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧ (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧ ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧ ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧ (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧ ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  first | exact @GlobalTheory.SgInfDD.DD_stable_dense | exact GlobalTheory.SgInfDD.DD_stable_dense | (intros; apply GlobalTheory.SgInfDD.DD_stable_dense <;> assumption)
