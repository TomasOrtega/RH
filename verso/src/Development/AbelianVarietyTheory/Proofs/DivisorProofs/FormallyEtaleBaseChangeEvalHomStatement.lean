import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHom
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormallyEtaleBaseChangeEvalHom.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.formallyEtale_baseChange_eval_hom : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  first | exact @GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | exact GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | (intros; apply GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor <;> assumption)
