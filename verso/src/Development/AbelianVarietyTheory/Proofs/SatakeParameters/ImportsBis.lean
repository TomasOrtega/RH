import Mathlib

namespace GlobalTheory.PolynomialNormBound

/- English proof (translation)
Introduce `l inst j m hj hdvd`. Establish `hl : l.Prime` using `inst.out`. Take `⟨v, u, hu, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one`. Establish `hvm : v < m`. Assume the negation of the conclusion as `h`.

Conclude with `hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)`. Establish `hunit : IsUnit (u : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl).mpr hu`. Take `⟨w, hw⟩` from `hunit`.

Use `⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩` and prove the remaining obligations. Establish `hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hsplit]`. Use `push_cast`. Rewrite using `[← hw]`. Combine the equalities or inequalities in the displayed calculation.
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
