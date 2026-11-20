import Mathlib

universe u_1

namespace GlobalTheory.PowEqOneValuation

/- English proof (translation)
Establish `h : v x ^ m = 1` using `by rw [← map_pow, hx, map_one]`. Conclude with `(pow_eq_one_iff_left hm).1 h`.
-/
theorem val_eq_one_of_pow_eq_one {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {m : ℕ} (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : v x = 1 := by
  have h : v x ^ m = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_left hm).1 h

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : 1 - u ^ (i + 1) = (1 - u) + u * (1 - u ^ i)` using `by ring`. Rewrite using `[e]`.

Use `v.map_add_lt h ?_` and prove the remaining obligations. Rewrite using `[map_mul, hu, one_mul]`. Conclude with `ih`.
-/
theorem val_one_sub_pow_lt {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {u : Ω} (hu : v u = 1) (h : v (1 - u) < 1) (i : ℕ) :
    v (1 - u ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - u ^ (i + 1) = (1 - u) + u * (1 - u ^ i) := by ring
    rw [e]
    refine v.map_add_lt h ?_
    rw [map_mul, hu, one_mul]
    exact ih

/- English proof (translation)
Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Apply `hm` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `v1` using `val_eq_one_of_pow_eq_one A.valuation hm0 h1`.

Establish `v2` using `val_eq_one_of_pow_eq_one A.valuation hm0 h2`. Establish `hz : ζ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at v1`. Assume the negation of the conclusion as `hne`.

Use `set u : Ω := ζ' / ζ with hu`. Establish `hu1 : u ≠ 1`. Introduce `e`. Apply `hne` to reduce the goal to its premises. Rewrite `e` using `[hu, div_eq_one_iff_eq hz]`.

Conclude with `e.symm`. Establish `hum : u ^ m = 1` using `by rw [hu, div_pow, h1, h2, div_one]`. Establish `vu : A.valuation u = 1` using `by rw [hu, map_div₀, v1, v2, div_one]`. Establish `v1u : A.valuation (1 - u) < 1`. Establish `e : 1 - u = (ζ - ζ') / ζ` using `by rw [hu, sub_div, div_self hz]`.

Rewrite using `[e, map_div₀, v1, div_one]`. Conclude with `h`. Establish `hs : ∑ i ∈ Finset.range m, u ^ i = 0`. Establish `g` using `geom_sum_mul u m`. Rewrite `g` using `[hum, sub_self]`.

Conclude with `(mul_eq_zero.1 g).resolve_right (sub_ne_zero.2 hu1)`. Establish `hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - u ^ i)`. Rewrite using `[Finset.sum_sub_distrib, hs]`. Simplify using the standard rewrite rules. Apply `hm` to reduce the goal to its premises.

Rewrite using `[hm']`. Conclude with `A.valuation.map_sum_lt one_ne_zero fun i _ => val_one_sub_pow_lt A.valuation vu v1u i`.
-/
theorem eq_of_pow_eq_one_of_valuation_sub_lt_one {Ω : Type u_1} [inst : Field Ω]
    (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω} (h1 : ζ ^ m = 1) (h2 : ζ' ^ m = 1)
    (hm : ¬ A.valuation (m : Ω) < 1) (h : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simp
  have v1 := val_eq_one_of_pow_eq_one A.valuation hm0 h1
  have v2 := val_eq_one_of_pow_eq_one A.valuation hm0 h2
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp at v1
  by_contra hne
  set u : Ω := ζ' / ζ with hu
  have hu1 : u ≠ 1 := by
    intro e
    apply hne
    rw [hu, div_eq_one_iff_eq hz] at e
    exact e.symm
  have hum : u ^ m = 1 := by rw [hu, div_pow, h1, h2, div_one]
  have vu : A.valuation u = 1 := by rw [hu, map_div₀, v1, v2, div_one]
  have v1u : A.valuation (1 - u) < 1 := by
    have e : 1 - u = (ζ - ζ') / ζ := by rw [hu, sub_div, div_self hz]
    rw [e, map_div₀, v1, div_one]
    exact h
  have hs : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have g := geom_sum_mul u m
    rw [hum, sub_self] at g
    exact (mul_eq_zero.1 g).resolve_right (sub_ne_zero.2 hu1)
  have hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  apply hm
  rw [hm']
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => val_one_sub_pow_lt A.valuation vu v1u i

end GlobalTheory.PowEqOneValuation
