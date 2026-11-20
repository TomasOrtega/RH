import Mathlib

namespace GlobalTheory.PolynomialNormBound

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by
  intro l inst j m hj hdvd
  have hl : l.Prime := inst.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one
  have hvm : v < m := by
    by_contra h
    exact hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)
  have hunit : IsUnit (u : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).mpr hu
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩
  have hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  rw [← hw]
  calc (l : ℤ_[l]) ^ v * ↑w * (↑w⁻¹ * (l : ℤ_[l]) ^ (m - 1 - v))
      = (l : ℤ_[l]) ^ v * ((↑w * ↑w⁻¹) * (l : ℤ_[l]) ^ (m - 1 - v)) := by ring
    _ = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by rw [Units.mul_inv, one_mul]

end GlobalTheory.PolynomialNormBound
