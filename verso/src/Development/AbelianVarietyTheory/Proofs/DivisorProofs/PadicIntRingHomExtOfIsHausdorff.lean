import Mathlib
open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem padicInt_ringHom_ext_of_isHausdorff : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  (f g : ℤ_[p] →+* O), f = g := by
  intro p _ O _ hH f g
  ext z
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hH _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (p : ℤ_[p]) ^ n * w + (z.appr n : ℕ) := by rw [mul_comm, hw]; ring
  have key : f z - g z = (p : O) ^ n * (f w - g w) := by
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast, mul_sub]
    abel
  rw [SModEq.zero, key, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory
