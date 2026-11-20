import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrix
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFourierInversionInvariantMatrix.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.fourier_inversion_invariant_matrix : ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | exact GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | (intros; apply GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving <;> assumption)
