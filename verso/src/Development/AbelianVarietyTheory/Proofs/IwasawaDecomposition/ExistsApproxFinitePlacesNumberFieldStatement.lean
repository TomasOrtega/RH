import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberField
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsApproxFinitePlacesNumberField.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField : ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)), Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 → ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  first | exact @GlobalTheory.exists_approx_finite_places | exact GlobalTheory.exists_approx_finite_places | (intros; apply GlobalTheory.exists_approx_finite_places <;> assumption)
