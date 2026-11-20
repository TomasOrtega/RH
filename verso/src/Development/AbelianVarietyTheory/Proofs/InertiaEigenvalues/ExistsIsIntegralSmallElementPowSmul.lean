import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc

/- English proof (translation)
Establish `hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Take `⟨n, hn⟩` from `WithTop.ne_top_iff_exists.1 hyt`. Establish `ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a`. Rewrite using `[ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]`.

Conclude with `ha`. Use `⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩` and prove the remaining obligations. Rewrite using `[IsDiscreteValuationRing.addVal_pow, ← hn]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dvr_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a y : O}
    (ha : a ∈ IsLocalRing.maximalIdeal O) (hy : y ≠ 0) : ∃ k : ℕ, y ∣ a ^ k := by
  have hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hyt
  have ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a := by
    rw [ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact ha
  refine ⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩
  rw [IsDiscreteValuationRing.addVal_pow, ← hn]
  calc ((n : ℕ∞)) = n • (1 : ℕ∞) := by simp
    _ ≤ n • IsDiscreteValuationRing.addVal O a := nsmul_le_nsmul_right ha1 n

/- English proof (translation)
Establish `hxE : IsIntegral K.E x` using `Algebra.IsIntegral.isIntegral x`. Take `⟨⟨m, hm⟩, hmx⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE`. Establish `hm0 : m ≠ 0` using `nonZeroDivisors.ne_zero hm`. Take `⟨k, w, hw⟩` from `dvr_dvd_pow ha.2.1 hm0`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x` using `rfl`. Establish `: (al K a ^ k) • x = algebraMap K.O B.A w * (m • x)`. Rewrite using `[← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap.mul (hsm ▸ hmx)`.
-/
theorem smul_pow_integral (K : UQ) (B : InvAlg K) (a : K.O) (ha : K.Small a) (x : B.A) :
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  have hxE : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
  obtain ⟨⟨m, hm⟩, hmx⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, w, hw⟩ := dvr_dvd_pow ha.2.1 hm0
  refine ⟨k, ?_⟩
  have hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x := rfl
  have : (al K a ^ k) • x = algebraMap K.O B.A w * (m • x) := by
    rw [← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]
  rw [this]
  exact isIntegral_algebraMap.mul (hsm ▸ hmx)

end GlobalTheory.UnitLemma.Desc
