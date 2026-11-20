import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffFrobeniusDoublePowerSeriesCongrBox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCoeffFrobeniusDoublePowerSeriesCongrBox.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.coeff_frobeniusDoublePowerSeries_congr_box : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H)) := by
  first | exact @GlobalTheory.CrysPrism.coeff_frob2_congr_box | exact GlobalTheory.CrysPrism.coeff_frob2_congr_box | (intros; apply GlobalTheory.CrysPrism.coeff_frob2_congr_box <;> assumption)
