import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

noncomputable section

open Matrix Finset Filter Topology
open scoped ContDiff ComplexOrder

namespace PositivityTheory.KcHalf2₂

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `v₀ hv₀`. Establish `hpd : (hOf v₀).PosDef` using `hv₀`. Establish `hc : Continuous fun p : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => (star p.2 ⬝ᵥ (hOf p.1 *ᵥ p.2)).re`. Unfold `hOf`.

Use `fun_prop`. Establish `hK : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1)` using `isCompact_sphere 0 1`. Establish `hev : ∀ᶠ v in 𝓝 v₀, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ (hOf v *ᵥ x)).re`. Use `hK.eventually_forall_of_forall_eventually fun x hx => ?_` and prove the remaining obligations. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hx` using `[mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hx`. Establish `h0 : 0 < (star x ⬝ᵥ (hOf v₀ *ᵥ x)).re` using `(Complex.pos_iff.1 (hpd.dotProduct_mulVec_pos hx0)).1`. Conclude with `hc.continuousAt (x := (v₀, x)) |>.eventually (lt_mem_nhds h0)`.

Use `filter_upwards [hev] with v hv`. Use `show (hOf v).PosDef`. Establish `hherm : (hOf v).IsHermitian` using `(hH n).2.2.2.2.1 v`. Use `PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_` and prove the remaining obligations. Establish `hnx : 0 < ‖x‖` using `norm_pos_iff.2 hx`.

Use `set u : Fin n → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu`. Establish `hus : u ∈ Metric.sphere (0 : Fin n → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnx.ne']`. Establish `hxu : x = ((‖x‖ : ℝ) : ℂ) • u`. Rewrite using `[hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnx.ne', Complex.ofReal_one, one_smul]`.

Establish `hq : star x ⬝ᵥ (hOf v *ᵥ x) = ((‖x‖ ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ (hOf v *ᵥ u))` using `by conv_lhs => rw [hxu]`. Rewrite using `[star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Complex.pos_iff]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Complex.re_ofReal_mul]`. Conclude with `mul_pos (by positivity) (hv u hus)`. Establish `h` using `hherm.im_star_dotProduct_mulVec_self x`. Conclude with `h.symm`.
-/
theorem isOpen_cone_of_hbFacts {n : ℕ} (hH : HbFacts) : IsOpen (cone n) := by
  rw [isOpen_iff_mem_nhds]
  intro v₀ hv₀
  have hpd : (hOf v₀).PosDef := hv₀
  have hc : Continuous fun p : (Fin n × Fin n → ℝ) × (Fin n → ℂ) =>
      (star p.2 ⬝ᵥ (hOf p.1 *ᵥ p.2)).re := by
    unfold hOf
    fun_prop
  have hK : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have hev : ∀ᶠ v in 𝓝 v₀, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ (hOf v *ᵥ x)).re := by
    refine hK.eventually_forall_of_forall_eventually fun x hx => ?_
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [mem_sphere_zero_iff_norm, norm_zero] at hx
      exact zero_ne_one hx
    have h0 : 0 < (star x ⬝ᵥ (hOf v₀ *ᵥ x)).re := (Complex.pos_iff.1 (hpd.dotProduct_mulVec_pos hx0)).1
    exact hc.continuousAt (x := (v₀, x)) |>.eventually (lt_mem_nhds h0)
  filter_upwards [hev] with v hv
  show (hOf v).PosDef
  have hherm : (hOf v).IsHermitian := (hH n).2.2.2.2.1 v
  refine PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u : Fin n → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
  have hus : u ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hnx.ne']
  have hxu : x = ((‖x‖ : ℝ) : ℂ) • u := by
    rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnx.ne', Complex.ofReal_one, one_smul]
  have hq : star x ⬝ᵥ (hOf v *ᵥ x) = ((‖x‖ ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ (hOf v *ᵥ u)) := by
    conv_lhs => rw [hxu]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
    push_cast
    ring
  rw [Complex.pos_iff]
  refine ⟨?_, ?_⟩
  · rw [hq, Complex.re_ofReal_mul]
    exact mul_pos (by positivity) (hv u hus)
  · have h := hherm.im_star_dotProduct_mulVec_self x
    exact h.symm

end PositivityTheory.KcHalf2₂
