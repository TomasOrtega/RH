import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendMvPolynomial
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDerivationExtendMvPolynomial.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.exists_derivation_extend_mvPolynomial : ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B), ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B), (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  first | exact @GlobalTheory.derivation_extend_mvPolynomial | exact GlobalTheory.derivation_extend_mvPolynomial | (intros; apply GlobalTheory.derivation_extend_mvPolynomial <;> assumption)
