import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the indicated hypotheses using the stated equalities.
-/
private theorem zpow_congr_mod {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  obtain ⟨k, hk⟩ := h.dvd
  have hz : ζ ^ (M : ℤ) = 1 := by
    rw [zpow_natCast, hζ]
  have hb : b = a + M * k := by
    omega
  rw [hb, zpow_add₀ (by rintro rfl; simp [zero_pow hM.ne'] at hζ), zpow_mul, hz, one_zpow, mul_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem eisF_congr_mod {K : Type} [Field K] [CharZero K] (j : ℕ) {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ b₁ b₂ n := by
  unfold eisF
  split_ifs
  · unfold const0 frc
    have hd : ((M : ℤ) ∣ a₁ ↔ (M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁]
    rw [zpow_congr_mod hM hζ h₂, show a₁ % (M : ℤ) = b₁ % M from h₁]
    simp only [hd]
  · unfold coefPos
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : ∀ x : ℤ, (x ≡ a₁ [ZMOD M] ↔ x ≡ b₁ [ZMOD M]) :=
      fun x => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    simp only [hc, zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)).neg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.smoothedEisenstein_congr_of_modEq :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K), 0 < M → ζ ^ M = 1 → ∀ {a₁ b₁ a₂ b₂ : ℤ}, a₁ ≡ b₁ [ZMOD M] → a₂ ≡ b₂ [ZMOD M] → smF c j M ζ a₁ a₂ = smF c j M ζ b₁ b₂ := by
  intro K _ _ c j M ζ hM hζ a₁ b₁ a₂ b₂ h₁ h₂
  funext n
  unfold smF
  rw [eisF_congr_mod j hM hζ h₁ h₂, eisF_congr_mod j hM hζ (h₁.mul_left c) (h₂.mul_left c)]
