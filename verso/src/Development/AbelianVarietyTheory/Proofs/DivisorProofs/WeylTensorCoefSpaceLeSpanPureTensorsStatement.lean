import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensors
import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.coefSpace_le_span_pure_tensors` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeylTensorCoefSpaceLeSpanPureTensors.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
