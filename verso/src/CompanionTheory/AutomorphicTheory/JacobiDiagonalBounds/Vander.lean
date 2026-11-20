import Mathlib

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem vander' (Q : ℕ) : ∃ lam : Fin (Q + 1) → Fin (Q + 1) → ℂ, ∀ (E : Type) [AddCommGroup E] [Module ℂ E]
    (a : Fin (Q + 1) → E) (q : Fin (Q + 1)),
    a q = ∑ s : Fin (Q + 1), lam q s • ∑ j : Fin (Q + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) • a j := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ,
      V = Matrix.vandermonde fun s => ((s : ℕ) : ℂ) := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    simpa [Fin.ext_iff] using hij
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  refine ⟨fun q s => (V⁻¹ : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q s, fun E _ _ a q => ?_⟩
  beta_reduce
  have hrow : ∀ j : Fin (Q + 1),
      ∑ s : Fin (Q + 1), V⁻¹ q s * ((s : ℕ) : ℂ) ^ (j : ℕ) = (1 : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℂ) q j := by
    intro j
    rw [← hinv, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hV, Matrix.vandermonde_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hrow, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

end Formalism.FourierDecayAlt.P.NormalFormRelations
