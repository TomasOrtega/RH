import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

/- English proof (translation)
Set `L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R` to `{ toFun := fun F => fun α => D (MvPowerSeries.coeff α F) map_add' := by`. Introduce `F G`. Use function extensionality and compare the values at `α`. Use `show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)`. Rewrite using `[map_add, map_add]`.

Use the proof step `map_smul' := by`. Introduce `n F`. Use function extensionality and compare the values at `α`. Use `show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)`. Rewrite using `[map_zsmul, map_zsmul] }`.

Establish `hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F)` using `fun _ _ => rfl`. Use `⟨Derivation.mk' L ?_, ?_⟩` and prove the remaining obligations. Introduce `F G`. Use extensionality with `α`. Rewrite using `[smul_eq_mul, smul_eq_mul, map_add]`.

Use `erw [hL]`. Rewrite using `[MvPowerSeries.coeff_mul, map_sum, MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `erw [hL, hL]`.

Conclude with `congrArg (_ + ·) (mul_comm _ _)`. Introduce `F α`. Both sides reduce to the same expression.
-/
theorem mvPowerSeries_derivation_coeffwise (σ R : Type) [CommRing R] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R),
      ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  classical
  let L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R :=
    { toFun := fun F => fun α => D (MvPowerSeries.coeff α F)
      map_add' := by
        intro F G
        funext α
        show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)
        rw [map_add, map_add]
      map_smul' := by
        intro n F
        funext α
        show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)
        rw [map_zsmul, map_zsmul] }
  have hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F) := fun _ _ => rfl
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro F G
    ext α
    rw [smul_eq_mul, smul_eq_mul, map_add]
    erw [hL]
    rw [MvPowerSeries.coeff_mul, map_sum,
      MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    erw [hL, hL]
    exact congrArg (_ + ·) (mul_comm _ _)
  · intro F α
    rfl

end GlobalTheory
