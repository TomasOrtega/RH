import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

/- English proof (translation)
Establish `hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r` using `fun _ _ _ => rfl`. Establish `hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r`. Introduce `ψ r`. Rewrite using `[scale, dif_pos hk]`. Conclude with `HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)`.

Rewrite using `[HahnSeries.C_mul_eq_smul]`. Use extensionality with `s`. Take `⟨r, rfl⟩ : ∃ r, s = a / d * r` from `⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩`. Rewrite using `[HahnSeries.coeff_smul]`. Simplify using `only [qD, sub]`.

Rewrite using `[hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qD_sub (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ) (hk : 0 < a / d)
    (φ : HahnSeries ℚ Ω) :
    qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  have hcm : ∀ (c : ℚ → Ω) (ψ : HahnSeries ℚ Ω) (r : ℚ), (cm c ψ).coeff r = c r * ψ.coeff r :=
    fun _ _ _ => rfl
  have hsc : ∀ (ψ : HahnSeries ℚ Ω) (r : ℚ), (scale (a / d) ψ).coeff (a / d * r) = ψ.coeff r := by
    intro ψ r
    rw [scale, dif_pos hk]
    exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (a / d) hk).toOrderEmbedding) (a := r)
  rw [HahnSeries.C_mul_eq_smul]
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = a / d * r := ⟨s / (a / d), (mul_div_cancel₀ s hk.ne').symm⟩
  rw [HahnSeries.coeff_smul]
  simp only [qD, sub]
  rw [hcm, hsc, hsc, hcm, hcm, hcm, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CyclotomicQExpansion
