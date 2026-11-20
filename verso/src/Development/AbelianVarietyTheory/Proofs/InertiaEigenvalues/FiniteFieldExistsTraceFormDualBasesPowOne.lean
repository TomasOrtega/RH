import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
