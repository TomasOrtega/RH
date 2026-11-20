import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

namespace GlobalTheory.UltrametricUnitNorm

section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)`.
-/
theorem norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1)` using `by ring`. Rewrite using `[e]`.

Use `norm_add_lt_one ?_ h` and prove the remaining obligations. Rewrite using `[norm_mul, hu, one_mul]` and apply the resulting hypothesis.
-/
theorem norm_pow_sub_one_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (i : ℕ) : ‖u ^ i - 1‖ < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
    rw [e]
    refine norm_add_lt_one ?_ h
    rwa [norm_mul, hu, one_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K) = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1)`. Rewrite using `[Finset.sum_range_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)`.
-/
theorem norm_geom_sub_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)

omit [IsUltrametricDist K] in
/- English proof (translation)
Establish `h : ‖x‖ ^ m = 1` using `by rw [← norm_pow, hx, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h`.
-/
theorem norm_eq_one_of_pow {x : K} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h

/- English proof (translation)
Establish `nζ` using `norm_eq_one_of_pow hm hζ`. Establish `nη` using `norm_eq_one_of_pow hm hη`. Establish `z0 : ζ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at nζ`.

Assume the negation of the conclusion as `hne`. Establish `hu : ‖η / ζ‖ = 1` using `by rw [norm_div, nζ, nη, div_one]`. Establish `hu1 : η / ζ - 1 = (η - ζ) / ζ` using `by field_simp`. Establish `hlt : ‖η / ζ - 1‖ < 1` using `by rwa [hu1, norm_div, nζ, div_one]`. Establish `hne' : η / ζ - 1 ≠ 0`.

Rewrite using `[hu1]`. Conclude with `div_ne_zero (sub_ne_zero.2 hne) z0`. Establish `hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0`. Use `geom_sum_mul (η / ζ) m` as an intermediate fact. Rewrite `this` using `[div_pow η ζ m, hη, hζ, div_one, sub_self]`.

Conclude with `(mul_eq_zero.1 this).resolve_right hne'`. Use `norm_geom_sub_lt hu hlt m` as an intermediate fact. Rewrite `this` using `[hs, zero_sub, norm_neg, hn]`. Conclude with `lt_irrefl _ this`.
-/
theorem eq_of_norm_sub_lt {m : ℕ} (hm : 0 < m) (hn : ‖(m : K)‖ = 1) {ζ η : K} (hζ : ζ ^ m = 1)
    (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  have nζ := norm_eq_one_of_pow hm hζ
  have nη := norm_eq_one_of_pow hm hη
  have z0 : ζ ≠ 0 := by
    rintro rfl
    simp at nζ
  by_contra hne
  have hu : ‖η / ζ‖ = 1 := by rw [norm_div, nζ, nη, div_one]
  have hu1 : η / ζ - 1 = (η - ζ) / ζ := by field_simp
  have hlt : ‖η / ζ - 1‖ < 1 := by rwa [hu1, norm_div, nζ, div_one]
  have hne' : η / ζ - 1 ≠ 0 := by
    rw [hu1]
    exact div_ne_zero (sub_ne_zero.2 hne) z0
  have hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0 := by
    have := geom_sum_mul (η / ζ) m
    rw [div_pow η ζ m, hη, hζ, div_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne'
  have := norm_geom_sub_lt hu hlt m
  rw [hs, zero_sub, norm_neg, hn] at this
  exact lt_irrefl _ this

end

/- English proof (translation)
Establish `e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l])` using `(map_natCast _ m).symm`. Rewrite using `[e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm`.
-/
theorem norm_natCast_eq_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hlm : ¬l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm

/- English proof (translation)
The claim follows from `eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h`.
-/
theorem root_eq_of_norm_sub_lt_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hm : 0 < m) (hlm : ¬l ∣ m)
    {ζ η : Formalism.BasicNotions.Loc.Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ :=
  eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h

end GlobalTheory.UltrametricUnitNorm
