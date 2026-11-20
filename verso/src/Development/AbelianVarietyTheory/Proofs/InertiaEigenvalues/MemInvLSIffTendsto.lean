import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

/- English proof (translation)
Establish `h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K)` using `by simp`. Establish `hl : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (l_ne_zero l)`. Establish `key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n = ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n)` using `fun m n => by`. Rewrite using `[h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm⟩`. Establish `h` using `(mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹`. Rewrite `h` using `[mul_zero]`. Use `h.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[key, inv_mul_cancel_left₀ (pow_pos hl m).ne']`.

Introduce `hf`. Take `⟨b, hb⟩` from `hf.bddAbove_range`. Establish `h` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)).mul_const b`. Rewrite `h` using `[zero_mul]`. Take `⟨m, hm⟩` from `(h.eventually (gt_mem_nhds zero_lt_one)).exists`.

Use `⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `(mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le`. Establish `h3` using `hf.const_mul (‖(l : K)‖ ^ m)`. Rewrite `h3` using `[mul_zero]`.

Conclude with `h3.congr fun n => (key m n).symm`.
-/
theorem mem_invL_S_iff_tendsto (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] (f : K⟦X⟧) :
    f ∈ invL l (S O K e) ↔ Tendsto (fun n => ‖coeff n f‖ * wS K e n) atTop (𝓝 0) := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  have key : ∀ m n : ℕ, ‖coeff n ((((l : S O K e) : K⟦X⟧)) ^ m * f)‖ * wS K e n =
      ‖(l : K)‖ ^ m * (‖coeff n f‖ * wS K e n) := fun m n => by
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  constructor
  · rintro ⟨m, hm⟩
    have h := (mem_S.1 hm).2.const_mul (‖(l : K)‖ ^ m)⁻¹
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [key, inv_mul_cancel_left₀ (pow_pos hl m).ne']
  · intro hf
    obtain ⟨b, hb⟩ := hf.bddAbove_range
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, mem_S.2 ⟨fun n => ?_, ?_⟩⟩
    · rw [key]
      exact (mul_le_mul_of_nonneg_left (hb ⟨n, rfl⟩) (pow_pos hl m).le).trans hm.le
    · have h3 := hf.const_mul (‖(l : K)‖ ^ m)
      rw [mul_zero] at h3
      exact h3.congr fun n => (key m n).symm

end GlobalTheory.BK
