import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeLaplacianVanishes
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
Apply `GlobalTheory.VdmHarm.vdm_pderiv_sum_and_laplacian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVandermondeLaplacianVanishes.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.vandermonde_laplacian_vanishes : ∀ r : ℕ, ∑ a : Fin r, MvPolynomial.pderiv (some a) (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ) = 0 ∧ ∑ a : Fin r, MvPolynomial.pderiv (some a) (MvPolynomial.pderiv (some a) (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ)) = 0 := by
  first | exact @GlobalTheory.VdmHarm.vdm_pderiv_sum_and_laplacian | exact GlobalTheory.VdmHarm.vdm_pderiv_sum_and_laplacian | (intros; apply GlobalTheory.VdmHarm.vdm_pderiv_sum_and_laplacian <;> assumption)
