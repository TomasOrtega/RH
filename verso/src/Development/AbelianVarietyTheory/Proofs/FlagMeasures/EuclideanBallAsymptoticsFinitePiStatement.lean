import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EuclideanBallAsymptoticsFinitePi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FEuclideanBallAsymptoticsFinitePi.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.euclideanBallAsymptotics_finite_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) → (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) → IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  first | exact @GlobalTheory.LeviIso.isRadial_pi | exact GlobalTheory.LeviIso.isRadial_pi | (intros; apply GlobalTheory.LeviIso.isRadial_pi <;> assumption)
