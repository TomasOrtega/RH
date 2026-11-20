import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPlurisubharmonicLocal.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.plurisubharmonic_local : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U → (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | exact GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally | (intros; apply GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally <;> assumption)
