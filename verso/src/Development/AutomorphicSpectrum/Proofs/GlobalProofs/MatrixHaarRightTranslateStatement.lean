import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MatrixHaarRightTranslate
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FMatrixHaarRightTranslate.lean&line=397#L397)
-/
theorem _root_.GlobalTheory.T.matrix_haar_right_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F => x * (g : Matrix (Fin m) (Fin m) F)) dx = ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧ (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F => (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) := by
  first | exact @GlobalTheory.CompanionTheory.QLScale.haar_mat_scale | exact GlobalTheory.CompanionTheory.QLScale.haar_mat_scale | (intros; apply GlobalTheory.CompanionTheory.QLScale.haar_mat_scale <;> assumption)
