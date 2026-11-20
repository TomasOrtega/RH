import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.weil_formula_integrable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWeilFormulaIntegrableComplex.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.weil_formula_integrable_complex : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  first | exact @GlobalTheory.weil_formula_integrable | exact GlobalTheory.weil_formula_integrable | (intros; apply GlobalTheory.weil_formula_integrable <;> assumption)
