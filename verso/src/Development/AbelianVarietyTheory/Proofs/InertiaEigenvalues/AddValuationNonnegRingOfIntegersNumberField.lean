import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ v a`. Establish `hZ : ∀ m : ℤ, 0 ≤ v (m : L)`. Introduce `m`. Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => simp [AddValuation.map_zero]`.

Consider the case `succ k ih`. Rewrite using `[Int.cast_add, Int.cast_one]`. Conclude with `AddValuation.map_le_add v ih (by rw [AddValuation.map_one])`. Consider the case `pred k ih`. Rewrite using `[Int.cast_sub, Int.cast_one]`.

Conclude with `AddValuation.map_le_sub v ih (by rw [AddValuation.map_one])`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Take `⟨f, hm, hf⟩` from `NumberField.RingOfIntegers.isIntegral_coe a`. Use `set x : L := (a : L) with hx`.

Establish `hxtop : v x ≠ ⊤` using `ne_top_of_lt hneg`. Take `⟨k, hk⟩` from `WithTop.ne_top_iff_exists.mp hxtop`. Establish `hk0 : k < 0`. Rewrite `hneg` using `[← hk]`. Conclude with `hneg` after adjusting the coercions.

Distinguish the cases in `hn : f.natDegree = 0`. Rewrite `hn` using `[Polynomial.natDegree_eq_zero]`. Take `⟨c, rfl⟩` from `hn`. Establish `hc : c = 1`. Establish `h1` using `hm.leadingCoeff`.

Rewrite `h1` using `[Polynomial.leadingCoeff_C]`. Then use the resulting hypothesis. Substitute `hc` using the available equality. Simplify using `at hf`. Simplify using `only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul, add_eq_zero_iff_eq_neg] at hf`. Use `apply_fun v at hf`.

Rewrite `hf` using `[AddValuation.map_neg, AddValuation.map_pow, ← hk]`. Establish `hlt : ((f.natDegree • k : ℤ) : WithTop ℤ) < v (∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * x ^ i)`. Apply `AddValuation.map_lt_sum v (WithTop.coe_ne_top)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`.

Rewrite using `[AddValuation.map_mul, AddValuation.map_pow, ← hk, eq_intCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]`. Establish `: (i : ℤ) < f.natDegree` using `by exact_mod_cast hi`. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = i • (k : WithTop ℤ) := by rw [WithTop.coe_nsmul]`. Use `_ ≤ v ((f.coeff i : ℤ) : L) + i • (k : WithTop ℤ) := le_add_of_nonneg_left (hZ _)`. Rewrite `hlt` using `[WithTop.coe_nsmul, hf]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem addValuation_nonneg_of_ringOfIntegers :
    ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L),
      0 ≤ v (a : L) := by
  intro L _ _ v a
  have hZ : ∀ m : ℤ, 0 ≤ v (m : L) := by
    intro m
    induction m using Int.induction_on with
    | zero => simp [AddValuation.map_zero]
    | succ k ih =>
      rw [Int.cast_add, Int.cast_one]
      exact AddValuation.map_le_add v ih (by rw [AddValuation.map_one])
    | pred k ih =>
      rw [Int.cast_sub, Int.cast_one]
      exact AddValuation.map_le_sub v ih (by rw [AddValuation.map_one])
  by_contra hneg
  push_neg at hneg
  obtain ⟨f, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  set x : L := (a : L) with hx
  have hxtop : v x ≠ ⊤ := ne_top_of_lt hneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hxtop
  have hk0 : k < 0 := by
    rw [← hk] at hneg
    exact_mod_cast hneg
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c = 1 := by
      have h1 := hm.leadingCoeff
      rwa [Polynomial.leadingCoeff_C] at h1
    subst hc
    simp at hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun v at hf
  rw [AddValuation.map_neg, AddValuation.map_pow, ← hk] at hf
  have hlt : ((f.natDegree • k : ℤ) : WithTop ℤ) <
      v (∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * x ^ i) := by
    apply AddValuation.map_lt_sum v (WithTop.coe_ne_top)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk, eq_intCast]
    calc ((f.natDegree • k : ℤ) : WithTop ℤ) < ((i • k : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_lt_coe, nsmul_eq_mul, nsmul_eq_mul]
          have : (i : ℤ) < f.natDegree := by exact_mod_cast hi
          nlinarith
      _ = i • (k : WithTop ℤ) := by rw [WithTop.coe_nsmul]
      _ ≤ v ((f.coeff i : ℤ) : L) + i • (k : WithTop ℤ) := le_add_of_nonneg_left (hZ _)
  rw [WithTop.coe_nsmul, hf] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory
