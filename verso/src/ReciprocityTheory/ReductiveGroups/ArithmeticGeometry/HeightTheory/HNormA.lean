import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HNm

/- English proof (translation)
Consider the cases of `a with`. Consider the case `top => simp at h`. Consider the case `coe x`. Consider the cases of `b with`. Consider the case `top => simp at h`.

Consider the case `coe y`. Establish `h' : x + y = 0` using `by exact_mod_cast h`. Establish `hx : 0 ≤ x` using `by exact_mod_cast ha`. Establish `hy : 0 ≤ y` using `by exact_mod_cast hb`. Conclude with `(show x = 0 by omega)` after adjusting the coercions.
-/
theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  cases a with
  | top => simp at h
  | coe x =>
    cases b with
    | top => simp at h
    | coe y =>
      have h' : x + y = 0 := by exact_mod_cast h
      have hx : 0 ≤ x := by exact_mod_cast ha
      have hy : 0 ≤ y := by exact_mod_cast hb
      exact_mod_cast (show x = 0 by omega)

/- English proof (translation)
Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Take `⟨m, hm⟩` from `WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)`. Establish `hm0 : m < 0` using `by rw [← hm] at hneg; exact_mod_cast hneg`. Take `⟨p, hpm, hp⟩` from `hx`.

Rewrite `hp` using `[hpm.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp`. Establish `hsum` using `eq_neg_of_add_eq_zero_left hp`. Establish `hlow : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤ w (∑ i ∈ Finset.range p.natDegree, algebraMap R L (p.coeff i) * x ^ i)`. Apply `w.map_le_sum` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[w.map_mul, w.map_pow, ← hm]`. Establish `ha` using `h0 (p.coeff i)`. Establish `hle : ((p.natDegree : ℤ) - 1) * m ≤ (i : ℤ) * m` using `mul_le_mul_of_nonpos_right (by omega) hm0.le`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hle` after adjusting the coercions. Use `_ = i • (m : WithTop ℤ) := by rw [← WithTop.coe_nsmul, nsmul_eq_mul]`. Use `_ ≤ w (algebraMap R L (p.coeff i)) + i • (m : WithTop ℤ) := le_add_of_nonneg_left ha`. Establish `hxn : w (x ^ p.natDegree) = (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ)`.

Rewrite using `[w.map_pow, ← hm, ← WithTop.coe_nsmul, nsmul_eq_mul]`. Establish `key : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤ (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ)`. Rewrite using `[← hxn, hsum, w.map_neg]`. Conclude with `hlow`. Establish `key'` using `WithTop.coe_le_coe.mp key`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nonneg_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : AddValuation L (WithTop ℤ)) (h0 : ∀ r : R, 0 ≤ w (algebraMap R L r)) {x : L}
    (hx : IsIntegral R x) : 0 ≤ w x := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
  have hm0 : m < 0 := by rw [← hm] at hneg; exact_mod_cast hneg
  obtain ⟨p, hpm, hp⟩ := hx
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  have hsum := eq_neg_of_add_eq_zero_left hp
  have hlow : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      w (∑ i ∈ Finset.range p.natDegree, algebraMap R L (p.coeff i) * x ^ i) := by
    apply w.map_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [w.map_mul, w.map_pow, ← hm]
    have ha := h0 (p.coeff i)
    have hle : ((p.natDegree : ℤ) - 1) * m ≤ (i : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by omega) hm0.le
    calc ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤ (((i : ℤ) * m : ℤ) : WithTop ℤ) := by
          exact_mod_cast hle
      _ = i • (m : WithTop ℤ) := by rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      _ ≤ w (algebraMap R L (p.coeff i)) + i • (m : WithTop ℤ) := le_add_of_nonneg_left ha
  have hxn : w (x ^ p.natDegree) = (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [w.map_pow, ← hm, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have key : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [← hxn, hsum, w.map_neg]; exact hlow
  have key' := WithTop.coe_le_coe.mp key
  nlinarith

end HNm

end ReciprocityTheory.ChartRestriction.G.T0
