import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FIsotropicSublatticeGramDeterminant.lean&line=284#L284)
-/
theorem _root_.GlobalTheory.T.isotropic_sublattice_gram_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → ∀ (m : ℕ) (b : Module.Basis (Fin m) ℤ I), m = 2 * Fintype.card Ψ * Module.finrank (𝓞 E) I ∧ (Matrix.of fun i j => (R.ip (R.P (b i : Λ)) (R.P (b j : Λ))).re).det = (R.nz σ I * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.IsoCovol.det_re_gram_eq <;> assumption)
