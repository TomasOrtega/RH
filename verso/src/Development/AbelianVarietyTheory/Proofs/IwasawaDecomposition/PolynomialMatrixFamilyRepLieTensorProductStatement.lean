import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodMetric.PolyRep.lie_tensor` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolynomialMatrixFamilyRepLieTensorProduct.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_tensor | exact GlobalTheory.GoodMetric.PolyRep.lie_tensor | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_tensor <;> assumption)
