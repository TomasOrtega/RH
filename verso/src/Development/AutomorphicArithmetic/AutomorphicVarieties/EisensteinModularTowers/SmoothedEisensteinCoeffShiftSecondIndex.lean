import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Establish `h0 : ζ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hζ` using `[zero_pow hM.ne']`. Conclude with `zero_ne_one hζ`. Take `⟨k, hk⟩` from `h.dvd`.

Establish `: y = x + (M : ℤ) * k` using `by linarith`. Rewrite using `[this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]`.
-/
private theorem zpow_cg {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD M]) : ζ ^ x = ζ ^ y := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨k, hk⟩ := h.dvd
  have : y = x + (M : ℤ) * k := by linarith
  rw [this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

/- English proof (translation)
Establish `h0 : ζ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hζ` using `[zero_pow hM.ne']`. Conclude with `zero_ne_one hζ`. Unfold `eisF`.

Use `split_ifs with hn`. Substitute `hn` using the available equality. Simplify using `only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]`. Unfold `const0`. Distinguish the cases in `hd : (M : ℤ) ∣ a₁`.

Establish `: ζ ^ (a₂ + e * a₁) = ζ ^ a₂` using `zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))`. Rewrite using `[this]`. Simplify using `only [if_neg hd]`. Unfold `coefPos`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d`. Rewrite using `[← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]`. Rewrite using `[mul_sub]`. Use `congr 1`.

Use `split_ifs with h`. Establish `: ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d)`. Rewrite using `[← zpow_add₀ h0]`. Apply `zpow_cg hM hζ` to reduce the goal to its premises. Establish `h2` using `((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`.

Use `split_ifs with h`. Establish `: ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d))`. Rewrite using `[← zpow_add₀ h0]`. Apply `zpow_cg hM hζ` to reduce the goal to its premises. Establish `h2` using `(((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`.
-/
private theorem eisF_shift {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ) (hM : 0 < M)
    (hζ : ζ ^ M = 1) (n : ℕ) :
    eisF j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * eisF j M ζ a₁ a₂ n := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  unfold eisF
  split_ifs with hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]
    unfold const0
    by_cases hd : (M : ℤ) ∣ a₁
    · have : ζ ^ (a₂ + e * a₁) = ζ ^ a₂ :=
        zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))
      rw [this]
    · simp only [if_neg hd]
  · unfold coefPos
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    rw [mul_sub]
    congr 1
    · split_ifs with h
      · have : ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := ((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)
          refine h2.trans ?_
          rw [show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]
    · split_ifs with h
      · have : ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d)) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := (((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg
          refine h2.trans ?_
          rw [show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]

/- English proof (translation)
Introduce `K _ _ c j M ζ a₁ a₂ e hM hζ n`. Unfold `smF`. Rewrite using `[show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ, eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.smoothedEisensteinCoeff_shift_second_index :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ), 0 < M → ζ ^ M = 1 → ∀ n : ℕ, smF c j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * smF c j M ζ a₁ a₂ n := by
  intro K _ _ c j M ζ a₁ a₂ e hM hζ n
  unfold smF
  rw [show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ,
    eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]
  ring
