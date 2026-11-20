import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWhittakerEqZeroOfNotAntitone.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  first | exact @GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | exact GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | (intros; apply GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone <;> assumption)
