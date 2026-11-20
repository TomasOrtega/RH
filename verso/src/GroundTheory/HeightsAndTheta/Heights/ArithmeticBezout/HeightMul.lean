import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

/- English proof (translation)
Introduce `K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂`. Unfold `chowHt`. Establish `hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) = mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ)`. Introduce `σ`. Rewrite using `[map_mul]`.

Conclude with `hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero]))) (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))`. Rewrite using `[finsum_log_gaussNorm_mul h₁ h₂]`. Repeatedly rewrite using `[hmah]`. Rewrite using `[← mul_add]`. Use `congr 1`.

Establish `hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) = ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) + ∑ σ : K →+* ℂ, (mahler (H.normA …`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chowHeightMul_of_mahlerMul (hM : MahlerMul.Statement) : ChowHeightMul.Statement := by
  intro K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂
  unfold chowHt
  have hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) =
      mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) := by
    intro σ
    rw [map_mul]
    exact hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero])))
      (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))
  rw [finsum_log_gaussNorm_mul h₁ h₂]
  simp_rw [hmah]
  rw [← mul_add]
  congr 1
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) +
      (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * δ₂ * (harmonic (n - 1) : ℝ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  rw [hs]
  ring

end

end GroundTheory.Heights₂.Heights
