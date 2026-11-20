import Mathlib

namespace GlobalTheory.RootsOfUnityInjective

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

It suffices to derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_map_eq_of_pow_eq_one {R k : Type} [CommRing R] [IsDomain R] [CommRing k] [IsDomain k]
    (π : R →+* k) {N : ℕ} (hN : (N : k) ≠ 0) {u w : R} (hu : u ^ N = 1) (hw : w ^ N = 1)
    (h : π u = π w) : u = w := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  have hgeom := geom_sum₂_mul u w N
  rw [hu, hw, sub_self] at hgeom
  rcases mul_eq_zero.mp hgeom with h0 | h0
  · exfalso
    have h1 := congrArg π h0
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, h] at h1
    have hpow : (π w) ^ N = 1 := by rw [← map_pow, hw, map_one]
    have hterm : ∀ i ∈ Finset.range N, π w ^ i * π w ^ (N - 1 - i) = π w ^ (N - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hN h2
    · have hw0 : π w ≠ 0 := by
        intro hz
        rw [hz, zero_pow hN0] at hpow
        exact zero_ne_one hpow
      exact pow_ne_zero _ hw0 h2
  · exact sub_eq_zero.mp h0

end GlobalTheory.RootsOfUnityInjective
