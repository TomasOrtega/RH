import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy`. Establish `hl : (l : K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] K)]`. Conclude with `(map_ne_zero (algebraMap ℚ_[l] K)).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)`. Establish `hE : E K l e ^ η • y ∈ D.M` using `hy.1`.

Establish `h0 : (l : K) ^ η • D.phi y ∈ D.MM` using `D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)`. Establish `h1 : (l : K) ^ η • D.phi y ∈ D.MMl` using `D.ext_mono (le_away _ _) h0`. Establish `hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e)`. Use `⟨η, ?_⟩` and prove the remaining obligations. Establish `: ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1`.

Rewrite using `[show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hl, one_pow, map_one]`. Rewrite using `[this]`. Conclude with `one_mem _`. Establish `h2` using `D.MMl.smul_mem ⟨_, hc⟩ h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Subalgebra.smul_def]`. Use function extensionality and compare the values at `τ i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]`. Rewrite using `[PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow, map_one, one_mul]`.
-/
theorem phi_mem_MMl_of_mem_Y : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
  have hE : E K l e ^ η • y ∈ D.M := hy.1
  have h0 : (l : K) ^ η • D.phi y ∈ D.MM := D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hE)
  have h1 : (l : K) ^ η • D.phi y ∈ D.MMl := D.ext_mono (le_away _ _) h0
  have hc : (C ((l : K)⁻¹ ^ η) : K⟦X⟧) ∈ invL l (S O K e) := by
    refine ⟨η, ?_⟩
    have : ((l : S O K e) : K⟦X⟧) ^ η * C ((l : K)⁻¹ ^ η) = 1 := by
      rw [show ((l : S O K e) : K⟦X⟧) = C (l : K) by simp, ← map_pow, ← map_mul, ← mul_pow,
        mul_inv_cancel₀ hl, one_pow, map_one]
    rw [this]; exact one_mem _
  have h2 := D.MMl.smul_mem ⟨_, hc⟩ h1
  convert h2 using 1
  rw [Subalgebra.smul_def]
  funext τ i
  simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_mk]
  rw [PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hl, one_pow,
    map_one, one_mul]

end GlobalTheory.BK
