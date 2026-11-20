import Mathlib

namespace GlobalTheory.RootsOfUnityInjective

/- English proof (translation)
Establish `hN0 : N ≠ 0`. Introduce and unpack `rfl`. Conclude with `hN Nat.cast_zero`. Establish `hgeom` using `geom_sum₂_mul u w N`. Rewrite `hgeom` using `[hu, hw, sub_self]`.

Break down `mul_eq_zero.mp hgeom with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `h1` using `congrArg π h0`. Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [map_mul, map_pow, h] at h1`.

Establish `hpow : (π w) ^ N = 1` using `by rw [← map_pow, hw, map_one]`. Establish `hterm : ∀ i ∈ Finset.range N, π w ^ i * π w ^ (N - 1 - i) = π w ^ (N - 1)`. Introduce `i hi`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `hN h2`.

Establish `hw0 : π w ≠ 0`. Introduce `hz`. Rewrite `hpow` using `[hz, zero_pow hN0]`. Conclude with `zero_ne_one hpow`. Conclude with `pow_ne_zero _ hw0 h2`.

Conclude with `sub_eq_zero.mp h0`.
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
