import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate

noncomputable section

namespace PositivityTheory.ThKOwn

open Filter Topology GlobalTheory.CompanionTheory.OM.SchDiff
open scoped SchwartzMap LineDeriv ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Set `l : ℝ →L[ℝ] V` to `ContinuousLinearMap.toSpanSingleton ℝ a`. Set `M : ℝ × V →L[ℝ] V` to `ContinuousLinearMap.snd ℝ ℝ V + l ∘L ContinuousLinearMap.fst ℝ ℝ V`. Establish `hM : ∀ q : ℝ × V, M q = q.2 + q.1 • a` using `fun q => rfl`. Establish `hF : ContDiff ℝ ∞ (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1))` using `contDiff_const.mul ((g.smooth ⊤).comp M.contDiff)`. Establish `hb` using `bound_mul_translate (A := fun _ : ℝ × V => (1 : ℂ)) (Function.HasTemperateGrowth.const _) g l 0`.

Establish `hrem` using `seminorm_remainder hF 0 hb (fun t => SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) (fun t => t • ∂_{a} g) (fun p => by`. Use function extensionality and compare the values at `x`. Rewrite using `[SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, one_mul]`. Use the proof step `rfl)`. Use the proof step `(fun v => by`.

Use function extensionality and compare the values at `x`. Establish `e : (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1)) = ⇑g ∘ M`. Use function extensionality and compare the values at `q`. Rewrite using `[one_mul]`. Both sides reduce to the same expression.

Rewrite using `[e, ((g.hasFDerivAt (M (0, x))).comp (0, x) M.hasFDerivAt).fderiv]`. Simplify using `[hM, SchwartzMap.lineDerivOp_apply_eq_fderiv])`. Rewrite using `[(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]`. Introduce and unpack `⟨k, n⟩ ε hε`. Take `⟨C, hC⟩` from `hrem k n`.

Establish `h1 : Tendsto (fun t : ℝ => C * ‖t‖) (𝓝 0) (𝓝 0)`. Simplify using `using (continuous_norm.tendsto (0 : ℝ)).const_mul C`. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds hε)), nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with t ht h2 h3`. Establish `ht0 : t ≠ 0` using `ht`. Establish `h4` using `hC t (mem_closedBall_zero_iff.1 h3)`.

Establish `e : t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g) - ∂_{a} g = ((t⁻¹ : ℝ) : ℂ) • (SchwartzMap.compSubConstCLM ℂ (-((0 + t) • a)) g - SchwartzMap.compSubConstCLM ℂ (-((0 : ℝ) • a)) g - t • ∂_{a} g)`. Use extensionality with `x`. Establish `: (t : ℂ) ≠ 0` using `by exact_mod_cast ht0`. Simplify using `only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, zero_add, zero_smul, neg_zero, sub_zero, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[SchwartzMap.schwartzSeminormFamily_apply, e, map_smul_eq_mul, Complex.norm_real, norm_inv]`. Use `lt_of_le_of_lt ?_ h2` and prove the remaining obligations. Establish `hn : 0 < ‖t‖` using `norm_pos_iff.2 ht0`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_dq_tendsto (g : 𝓢(V, ℂ)) (a : V) :
    Tendsto (fun t : ℝ => t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g)) (𝓝[≠] 0) (𝓝 (∂_{a} g)) := by
  let l : ℝ →L[ℝ] V := ContinuousLinearMap.toSpanSingleton ℝ a
  let M : ℝ × V →L[ℝ] V := ContinuousLinearMap.snd ℝ ℝ V + l ∘L ContinuousLinearMap.fst ℝ ℝ V
  have hM : ∀ q : ℝ × V, M q = q.2 + q.1 • a := fun q => rfl
  have hF : ContDiff ℝ ∞ (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1)) :=
    contDiff_const.mul ((g.smooth ⊤).comp M.contDiff)
  have hb := bound_mul_translate (A := fun _ : ℝ × V => (1 : ℂ)) (Function.HasTemperateGrowth.const _) g l 0
  have hrem := seminorm_remainder hF 0 hb (fun t => SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) (fun t => t • ∂_{a} g)
    (fun p => by
      funext x
      rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, one_mul]
      rfl)
    (fun v => by
      funext x
      have e : (fun q : ℝ × V => (1 : ℂ) * g (q.2 + l q.1)) = ⇑g ∘ M := by
        funext q
        rw [one_mul]
        rfl
      rw [e, ((g.hasFDerivAt (M (0, x))).comp (0, x) M.hasFDerivAt).fderiv]
      simp [hM, SchwartzMap.lineDerivOp_apply_eq_fderiv])
  rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C, hC⟩ := hrem k n
  have h1 : Tendsto (fun t : ℝ => C * ‖t‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℝ)).const_mul C
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds hε)),
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with t ht h2 h3
  have ht0 : t ≠ 0 := ht
  have h4 := hC t (mem_closedBall_zero_iff.1 h3)
  have e : t⁻¹ • (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g - g) - ∂_{a} g =
      ((t⁻¹ : ℝ) : ℂ) • (SchwartzMap.compSubConstCLM ℂ (-((0 + t) • a)) g -
        SchwartzMap.compSubConstCLM ℂ (-((0 : ℝ) • a)) g - t • ∂_{a} g) := by
    ext x
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.compSubConstCLM_apply, zero_add, zero_smul,
      neg_zero, sub_zero, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
    field_simp
  rw [SchwartzMap.schwartzSeminormFamily_apply, e, map_smul_eq_mul, Complex.norm_real, norm_inv]
  refine lt_of_le_of_lt ?_ h2
  have hn : 0 < ‖t‖ := norm_pos_iff.2 ht0
  calc _ ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
    _ = _ := by field_simp

end PositivityTheory.ThKOwn

end
