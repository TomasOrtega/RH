import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussLatticeCoords

/- English proof (translation)
Establish `h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ)`. Use extensionality with `j`. Simplify using `[intVec, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[h, Matrix.mulVec_sum, WithLp.toLp_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]`.
-/
theorem toLp_mulVec_intVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  have h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_sum, WithLp.toLp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]

end PGaussLatticeCoords

open PGaussLatticeCoords in

/- English proof (translation)
Introduce `g B hB`. Use `⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩` and prove the remaining obligations. Rewrite using `[toLp_mulVec_intVec]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hx`.

Conclude with `⟨c, by rw [toLp_mulVec_intVec, hc]⟩`. Establish `hk : B *ᵥ intVec k = B *ᵥ intVec k'` using `hkk'`. Establish `hu : IsUnit B.det` using `isUnit_iff_ne_zero.2 hB`. Establish `hv : intVec k = intVec k'`. Use `congrArg (fun v => B⁻¹ *ᵥ v) hk` as an intermediate fact.

Simplify `this` using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec]`. Use function extensionality and compare the values at `i`. Conclude with `Int.cast_injective (congrFun hv i)`.
-/
theorem GaussLatticeCoords.proof : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)

end GroundTheory.Heights₂.Heights
