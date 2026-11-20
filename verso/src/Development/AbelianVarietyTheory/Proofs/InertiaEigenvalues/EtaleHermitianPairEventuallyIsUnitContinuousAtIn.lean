import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Set `b` to `Module.finBasis F K`. Set `ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F` to `Algebra.leftMulMatrix b`. Establish `hι : Continuous ι` using `IsModuleTopology.continuous_of_linearMap ι.toLinearMap`. Establish `hdet : Continuous fun a : K => (ι a).det` using `(continuous_id.matrix_det).comp hι`. Establish `h1 : (ι 1).det ≠ 0` using `by simp`.

Establish `hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0` using `hdet.continuousAt.eventually_ne h1`. Establish `hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a`. Introduce `a ha`. Establish `hn : Algebra.norm F a ≠ 0` using `by rw [Algebra.norm_eq_matrix_det b]; exact ha`. Rewrite `hn` using `[Algebra.norm_apply]`.

Establish `hu : IsUnit (Algebra.lmul F K a)`. Rewrite using `[LinearMap.isUnit_iff_isUnit_det]`. Conclude with `hn.isUnit`. Take `⟨c, hc⟩` from `((Module.End.isUnit_iff _).1 hu).2 1`. Conclude with `IsUnit.of_mul_eq_one c (by simpa using hc)`.

Establish `hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a` using `hev.mono hunit`. Use `⟨hev', ?_⟩` and prove the remaining obligations. Set `g : K → K` to `fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)`. Establish `hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a)`. Introduce `a ha`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← map_mul, Ring.inverse_mul_cancel a ha, map_one]`. Establish `heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse` using `by filter_upwards [hev'] with a ha`. Simplify using `only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]`.

Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations. Establish `hsymm : Continuous b.equivFun.symm` using `LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap`. Establish `hdet1 : ContinuousAt Ring.inverse (ι 1).det`. Establish `: (ι 1).det = 1` using `by simp`. Rewrite using `[this]`.

Establish `: (Ring.inverse : F → F) = Inv.inv` using `funext Ring.inverse_eq_inv`. Rewrite using `[this]`. Conclude with `continuousAt_inv₀ one_ne_zero`. Establish `hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1` using `(continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt`. Establish `hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1` using `continuous_id.matrix_mulVec continuous_const`.

Conclude with `hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)`.
-/
theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

/- English proof (translation)
Introduce `F _ _ _ _ _ A` and use `units_near_one_inverse_continuousAt F A.K`.
-/
theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
