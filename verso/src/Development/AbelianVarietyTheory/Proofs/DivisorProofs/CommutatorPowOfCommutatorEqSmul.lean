import Mathlib

namespace GlobalTheory.CommutatorPowerFormula

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem commutator_pow_of_commutator_eq_smul {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ}
    (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : H * X ^ (n + 1) - X ^ (n + 1) * H
        = (H * X ^ n - X ^ n * H) * X + X ^ n * (H * X - X * H) := by
      rw [pow_succ]
      noncomm_ring
    rw [e, ih, h, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← add_smul]
    congr 1
    push_cast
    ring

end GlobalTheory.CommutatorPowerFormula
