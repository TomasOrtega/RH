import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FISupMonomialHolderLogConvex.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.gaussNormAcris_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_basic_values | exact GlobalTheory.PMon.Gauss.gC_basic_values | (intros; apply GlobalTheory.PMon.Gauss.gC_basic_values <;> assumption)
