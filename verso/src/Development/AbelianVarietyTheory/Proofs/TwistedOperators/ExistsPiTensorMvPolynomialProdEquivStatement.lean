import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsPiTensorMvPolynomialProdEquiv.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.exists_piTensor_mvPolynomial_prod_equiv : ∀ (ι σ : Type) [Fintype ι], ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, ∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  first | exact @GlobalTheory.PolyTensor.exists_piTensor_equiv | exact GlobalTheory.PolyTensor.exists_piTensor_equiv | (intros; apply GlobalTheory.PolyTensor.exists_piTensor_equiv <;> assumption)
