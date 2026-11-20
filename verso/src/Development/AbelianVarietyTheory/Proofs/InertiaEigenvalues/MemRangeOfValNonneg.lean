import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Conclude with `⟨0, by simp [hz]⟩`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0` using `by simpa using hz`. Establish `hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1`. Unfold `val at h`.

Rewrite using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one hle`. Conclude with `⟨a, ha⟩`.
-/
theorem mem_range_of_val_nonneg (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0 := by simpa using hz
  have hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1 := by
    unfold val at h
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact ⟨a, ha⟩

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha, val]`. Unfold `val`. Establish `h1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) a`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0`.

Simplify using `using ha`. Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using ha
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/- English proof (translation)
Apply `mem_range_of_val_nonneg` to reduce the goal to its premises. Rewrite using `[hU.2.2.1]`. Conclude with `val_algebraMap_nonneg K a`.
-/
theorem exists_int_image {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by
  apply mem_range_of_val_nonneg
  rw [hU.2.2.1]
  exact val_algebraMap_nonneg K a

end GlobalTheory.UnitLemma.Unr
