import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLift
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DworkLift.exists_frobenius_compatible_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFrobeniusCompatibleLift.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_frobenius_compatible_wittVector_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
