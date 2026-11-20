import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

/- English proof (translation)
Introduce `K _ s y y' b hb h`. Establish `key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j`. Introduce `i j hk`. Rewrite using `[h, Matrix.mul_apply, Finset.sum_eq_single j]`. Simplify using `[upU]`.

Introduce `k _ hkj`. Break down `lt_or_gt_of_ne hkj with h1 | h1` into its components or cases. Rewrite using `[hk k h1, zero_mul]`. Simplify using `[upU, not_lt.mpr h1.le, hkj]`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ j) hj`. Establish `low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0`. Introduce `i N`. Proceed by induction on `N with`. Consider the case `zero => intro j hj`.

Conclude with `absurd hj (Nat.not_lt_zero _)`. Consider the case `succ N ih`. Introduce `j hj hji`. Rewrite using `[← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]`. Simplify using `[upU, not_lt.mpr hji.le, hji.ne']`.

Establish `hb1 : b = 1`. Use extensionality with `i j`. Break down `lt_trichotomy i j with h1 | rfl | h1` into its components or cases. Rewrite using `[hb i j h1, Matrix.one_apply_ne h1.ne]`. Rewrite using `[← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]`.

Simplify using `[upU]`. Rewrite using `[low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']`. Rewrite `h` using `[hb1, Matrix.one_mul]`. Use function extensionality and compare the values at `⟨⟨c, a⟩, hac⟩`. Establish `hac' : a < c` using `hac`.

Use `congrFun (congrFun h a) c` as an intermediate fact. Simplify `this` using `[upU, hac']`.
-/
theorem upU_unique_of_lower : ∀ (K : Type) [Field K] (s : ℕ) (y y' : Low s → K) (b : Matrix (Fin s) (Fin s) K),
    (∀ i j, i < j → b i j = 0) → upU y = b * upU y' → y = y' := by
  intro K _ s y y' b hb h
  have key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j := by
    intro i j hk
    rw [h, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [upU]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h1 | h1
      · rw [hk k h1, zero_mul]
      · simp [upU, not_lt.mpr h1.le, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0 := by
    intro i N
    induction N with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hji
      rw [← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]
      simp [upU, not_lt.mpr hji.le, hji.ne']
  have hb1 : b = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hb i j h1, Matrix.one_apply_ne h1.ne]
    · rw [← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]
      simp [upU]
    · rw [low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']
  rw [hb1, Matrix.one_mul] at h
  funext ⟨⟨c, a⟩, hac⟩
  have hac' : a < c := hac
  have := congrFun (congrFun h a) c
  simpa [upU, hac'] using this

end GlobalTheory.FlagCell2
