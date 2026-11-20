import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsBiorthogonalFrameOfSaturatedFlag.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  first | exact @GlobalTheory.RadCov.exists_biorth_of_saturated_flag | exact GlobalTheory.RadCov.exists_biorth_of_saturated_flag | (intros; apply GlobalTheory.RadCov.exists_biorth_of_saturated_flag <;> assumption)
