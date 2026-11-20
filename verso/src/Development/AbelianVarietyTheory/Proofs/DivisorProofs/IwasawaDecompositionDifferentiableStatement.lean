import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCell.exists_lu_differentiable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIwasawaDecompositionDifferentiable.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.iwasawa_decomposition_differentiable : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ), ∃ (φ : (Low m → ℂ) → Low m → ℂ) (B : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ), ∀ x : Low m → ℂ, (∀ l : Fin (m + 1), ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0) → (B x).BlockTriangular id ∧ IsUnit (B x).det ∧ g * uni x = uni (φ x) * B x ∧ DifferentiableAt ℂ φ x ∧ ∀ a c, DifferentiableAt ℂ (fun y => B y a c) x := by
  first | exact @GlobalTheory.FlagCell.exists_lu_differentiable | exact GlobalTheory.FlagCell.exists_lu_differentiable | (intros; apply GlobalTheory.FlagCell.exists_lu_differentiable <;> assumption)
