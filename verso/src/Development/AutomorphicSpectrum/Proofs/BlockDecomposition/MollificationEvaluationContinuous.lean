import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolBounded

open GlobalTheory.CompanionTheory.SobGL.HaarDom

variable {n : ℕ}

/- English proof (translation)
The claim follows from `hφ.comp (continuous_const.matrix_mul (Units.continuous_val.comp continuous_inv))`.
-/
theorem kernel_continuous {φ : Mat n → ℝ} (hφ : Continuous φ) (z : Mat n) :
    Continuous fun u : G n => φ (z * (u⁻¹ : G n).val) :=
  hφ.comp (continuous_const.matrix_mul (Units.continuous_val.comp continuous_inv))

/- English proof (translation)
Take `⟨-, hK, hKs⟩` from `hφ`. Establish `unit_of : ∀ w ∈ GLs n, ∃ y : G n, y.val = w`. Introduce `w hw`. Establish `hd : IsUnit w` using `(Matrix.isUnit_iff_isUnit_det w).2 (isUnit_iff_ne_zero.2 hw)`. Take `⟨y, hy⟩` from `hd`.

Conclude with `⟨y, hy⟩`. Take `⟨zG, rfl⟩` from `unit_of z hz`. Establish `hS : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ)`. Use `(isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_ |>.2 hK` and prove the remaining obligations. Introduce `w hw`.

Take `⟨y, hy⟩` from `unit_of w (hKs hw)`. Conclude with `⟨y, hy⟩`. Establish `hI : IsCompact ((fun w : G n => w⁻¹ * zG) '' ((Units.val : G n → Mat n) ⁻¹' tsupport φ))` using `hS.image (continuous_inv.mul continuous_const)`. Use `HasCompactSupport.intro hI fun u hu => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Use `hu ⟨zG * u⁻¹, ?_, by group⟩` and prove the remaining obligations. Establish `: (zG * u⁻¹).val ∈ Function.support φ`. Simplify `hne` using `[Function.mem_support]`. Conclude with `subset_tsupport φ this`.
-/
theorem kernel_hasCompactSupport {φ : Mat n → ℝ} (hφ : IsTest φ) {z : Mat n} (hz : z ∈ GLs n) :
    HasCompactSupport fun u : G n => φ (z * (u⁻¹ : G n).val) := by
  obtain ⟨-, hK, hKs⟩ := hφ
  have unit_of : ∀ w ∈ GLs n, ∃ y : G n, y.val = w := by
    intro w hw
    have hd : IsUnit w := (Matrix.isUnit_iff_isUnit_det w).2 (isUnit_iff_ne_zero.2 hw)
    obtain ⟨y, hy⟩ := hd
    exact ⟨y, hy⟩
  obtain ⟨zG, rfl⟩ := unit_of z hz
  have hS : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_ |>.2 hK
    intro w hw
    obtain ⟨y, hy⟩ := unit_of w (hKs hw)
    exact ⟨y, hy⟩
  have hI : IsCompact ((fun w : G n => w⁻¹ * zG) '' ((Units.val : G n → Mat n) ⁻¹' tsupport φ)) :=
    hS.image (continuous_inv.mul continuous_const)
  refine HasCompactSupport.intro hI fun u hu => ?_
  by_contra hne
  refine hu ⟨zG * u⁻¹, ?_, by group⟩
  have : (zG * u⁻¹).val ∈ Function.support φ := by
    simpa [Function.mem_support] using hne
  exact subset_tsupport φ this

/- English proof (translation)
Introduce `n _ _ μ _ V _ _ _ _ φ hφ z hz`. Use `set g : G n → ℝ := fun u => φ (z * (u⁻¹ : G n).val) with hgdef`. Establish `hgc : Continuous g` using `kernel_continuous hφ.1.continuous z`. Establish `hg2 : MemLp g 2 μ` using `hgc.memLp_of_hasCompactSupport (kernel_hasCompactSupport hφ hz)`. Establish `hmem : ∀ x : Lp V 2 μ, MemLp (g • (x : G n → V)) 1 μ` using `fun x => (Lp.memLp x).smul hg2`.

Establish `hint : ∀ x : Lp V 2 μ, Integrable (fun u => g u • (x : G n → V) u) μ` using `fun x => memLp_one_iff_integrable.1 (hmem x)`. Establish `hb : ∀ x : Lp V 2 μ, ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ (eLpNorm g 2 μ).toReal * ‖x‖`. Introduce `x`. Establish `h1 : eLpNorm (g • (x : G n → V)) 1 μ ≤ eLpNorm g 2 μ * eLpNorm x 2 μ` using `eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable x) hg2.1`. Establish `h2 : ∫ u, ‖g u • (x : G n → V) u‖ ∂μ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal`.

Rewrite using `[eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm (hint x).1]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.toReal_mul, Lp.norm_def]`. Set `Lin : Lp V 2 μ →ₗ[ℝ] V` to `{ toFun := fun x => ∫ u, g u • (x : G n → V) u ∂μ map_add' := fun x y => by`.

Rewrite using `[← integral_add (hint x) (hint y)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_add x y] with u hu`. Rewrite using `[hu, Pi.add_apply, smul_add]`. Use the proof step `map_smul' := fun c x => by`.

Rewrite using `[RingHom.id_apply, ← integral_smul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_smul c x] with u hu`. Rewrite using `[hu, Pi.smul_apply, smul_comm] }`. Conclude with `⟨Lin.mkContinuous _ hb, fun x => rfl⟩`.
-/
theorem mol_bounded : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ z ∈ GLs n,
      ∃ L : Lp V 2 μ →L[ℝ] V, ∀ x : Lp V 2 μ, L x = Mol μ φ (⇑x) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ z hz
  set g : G n → ℝ := fun u => φ (z * (u⁻¹ : G n).val) with hgdef
  have hgc : Continuous g := kernel_continuous hφ.1.continuous z
  have hg2 : MemLp g 2 μ := hgc.memLp_of_hasCompactSupport (kernel_hasCompactSupport hφ hz)
  have hmem : ∀ x : Lp V 2 μ, MemLp (g • (x : G n → V)) 1 μ := fun x =>
    (Lp.memLp x).smul hg2
  have hint : ∀ x : Lp V 2 μ, Integrable (fun u => g u • (x : G n → V) u) μ := fun x =>
    memLp_one_iff_integrable.1 (hmem x)
  have hb : ∀ x : Lp V 2 μ,
      ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ (eLpNorm g 2 μ).toReal * ‖x‖ := by
    intro x
    have h1 : eLpNorm (g • (x : G n → V)) 1 μ ≤ eLpNorm g 2 μ * eLpNorm x 2 μ :=
      eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable x) hg2.1
    have h2 : ∫ u, ‖g u • (x : G n → V) u‖ ∂μ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm (hint x).1]
      rfl
    calc ‖∫ u, g u • (x : G n → V) u ∂μ‖ ≤ ∫ u, ‖g u • (x : G n → V) u‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = (eLpNorm (g • (x : G n → V)) 1 μ).toReal := h2
      _ ≤ (eLpNorm g 2 μ * eLpNorm x 2 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hg2.2.ne (Lp.eLpNorm_ne_top x)) h1
      _ = (eLpNorm g 2 μ).toReal * ‖x‖ := by
          rw [ENNReal.toReal_mul, Lp.norm_def]
  let Lin : Lp V 2 μ →ₗ[ℝ] V :=
    { toFun := fun x => ∫ u, g u • (x : G n → V) u ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hint x) (hint y)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add x y] with u hu
        rw [hu, Pi.add_apply, smul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c x] with u hu
        rw [hu, Pi.smul_apply, smul_comm] }
  exact ⟨Lin.mkContinuous _ hb, fun x => rfl⟩

end GlobalTheory.CompanionTheory.PresSobA.MolBounded
