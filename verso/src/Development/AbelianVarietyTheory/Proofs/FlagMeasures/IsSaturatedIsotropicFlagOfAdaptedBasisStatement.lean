import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsSaturatedIsotropicFlagOfAdaptedBasis.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → IsSatFlag I (lamX I (1, xf)) j S := by
  first | exact @GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | exact GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted | (intros; apply GlobalTheory.FlagBase.AdSat.isSatFlag_of_isAdapted <;> assumption)
