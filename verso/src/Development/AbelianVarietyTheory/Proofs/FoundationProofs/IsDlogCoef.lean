import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivativeCyclotomicMul
open GlobalTheory.K5 Polynomial

noncomputable section
namespace GlobalTheory.K5.DlogCoef

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem smul_mk (J : Ideal (On p n)) (a b : On p n) :
    a • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (a * b) := by
  first
  | rfl
  | exact (Submodule.Quotient.mk_smul _ _ _).symm
  | simp [Algebra.smul_def]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_pow (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (r c : On p n) (h : D r = Ideal.Quotient.mk J (c * r)) (i : ℕ) :
    D (r ^ i) = Ideal.Quotient.mk J ((i : On p n) * c * r ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, h, smul_mk, smul_mk, ← map_add]
    congr 1
    push_cast
    ring

end GlobalTheory.K5.DlogCoef
