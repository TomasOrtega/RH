import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Unfold `val at h`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0` using `by simpa using he`. Rewrite using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/- English proof (translation)
Distinguish the cases in `hx : algebraMap K.O K.E x = 0`. Rewrite using `[hx]`. Unfold `val`. Simplify using the standard rewrite rules. Unfold `val`.

Establish `h1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0` using `by simpa using hx`. Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/- English proof (translation)
Distinguish the cases in `hx : algebraMap K.O K.E x = 0`. Conclude with `⟨0, by rw [hx, map_zero, map_zero]⟩`. Establish `hφ : φ (algebraMap K.O K.E x) ≠ 0` using `by simpa using hx`. Establish `hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x))`. Rewrite using `[hU.2.2.1]`.

Conclude with `val_nonneg_of_int K x`. Conclude with `IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)`.
-/
theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
