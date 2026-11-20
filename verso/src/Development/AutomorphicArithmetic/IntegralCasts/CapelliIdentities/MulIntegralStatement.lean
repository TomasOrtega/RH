import Mathlib

namespace OneParameterGroupMulIntegral
open intervalIntegral

/- English proof (translation)
Use `(ContinuousLinearMap.mul ℝ A c).intervalIntegral_comp_comm (μ := MeasureTheory.volume) (a := a) (b := b) (f := f)` as an intermediate fact. Simplify using `using (this hf).symm`.
-/
private lemma mul_integral {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : A) (f : ℝ → A) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    c * (∫ s in a..b, f s) = ∫ s in a..b, c * f s := by
  have := (ContinuousLinearMap.mul ℝ A c).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (a := a) (b := b) (f := f)
  simpa using (this hf).symm

end OneParameterGroupMulIntegral

open OneParameterGroupMulIntegral in
/- English proof (translation)
Introduce `W _ _ _ φ hc h0 hmul`. Take `⟨ε, εpos, hε⟩` from `Metric.continuous_iff.mp hc 0 (1/2) (by norm_num)`. Use `set δ : ℝ := ε / 2 with hδ`. Establish `δpos : 0 < δ` using `by positivity`. Use `set A : W →L[ℂ] W := ∫ s in (0:ℝ)..δ, φ s with hA`.

Establish `hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b` using `fun a b => hc.intervalIntegrable a b`. Establish `hest : ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ 1/2 * δ`. Establish `e1 : A - δ • (1 : W →L[ℂ] W) = ∫ s in (0:ℝ)..δ, (φ s - 1)`. Rewrite using `[intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const, intervalIntegral.integral_const]`. Apply the tactic sequence `simp <;> rfl`.

Rewrite using `[e1]`. Use `intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1/2) (f := fun s => φ s - 1) (by` as an intermediate fact. Introduce `x hx`. Rewrite `hx` using `[Set.uIoc_of_le δpos.le]`. Establish `hxd : dist x 0 < ε`.

Rewrite using `[Real.dist_eq, sub_zero, abs_of_pos hx.1]`. Combine the linear relations using `[hx.2]`. Use `hε x hxd` as an intermediate fact. Rewrite `this` using `[dist_eq_norm, h0]`. Conclude with `this.le)`.

Simplify `this` using `[abs_of_pos δpos]`. Establish `hsmall : ‖1 - δ⁻¹ • A‖ < 1`. Establish `: 1 - δ⁻¹ • A = -(δ⁻¹ • (A - δ • (1 : W →L[ℂ] W)))`. Rewrite using `[smul_sub, smul_smul, inv_mul_cancel₀ δpos.ne']`. Simplify using the standard rewrite rules.

Rewrite using `[this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr δpos)]`. Combine the equalities or inequalities in the displayed calculation. Use `set u := Units.oneSub (1 - δ⁻¹ • A) hsmall`. Establish `hu : (u : W →L[ℂ] W) = δ⁻¹ • A` using `by simp [u, Units.val_oneSub]`. Use `set B : W →L[ℂ] W := δ⁻¹ • ((u⁻¹ : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)`.

Establish `hAB : A * B = 1`. Simplify using `only [B, mul_smul_comm, ← smul_mul_assoc, ← hu]`. Conclude with `u.mul_inv`. Use `set F : ℝ → W →L[ℂ] W := fun u => ∫ s in (0:ℝ)..u, φ s`. Establish `key : ∀ t, φ t = (F (t + δ) - F t) * B`.

Introduce `t`. Establish `h1 : φ t * A = F (t + δ) - F t`. Rewrite using `[hA, mul_integral _ _ _ _ (hint 0 δ)]`. Establish `: (fun s => φ t * φ s) = fun s => φ (t + s)`. Use function extensionality and compare the values at `s`.

Rewrite using `[hmul]`. Rewrite using `[this, intervalIntegral.integral_comp_add_left (fun s => φ s) t]`. Simplify using `only [add_zero, F]`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hint 0 (t + δ)) (hint 0 t)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hF : ∀ x, HasDerivAt F (φ x) x` using `fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt`. Establish `hd : HasDerivAt (fun t => (F (t + δ) - F t) * B) ((φ (0 + δ) - φ 0) * B) 0`. Apply `HasDerivAt.mul_const` to reduce the goal to its premises. Apply `HasDerivAt.sub` to reduce the goal to its premises. Conclude with `(hF (0 + δ)).comp_add_const 0 δ`.

Conclude with `hF 0`. Establish `: φ = fun t => (F (t + δ) - F t) * B` using `funext key`. Rewrite using `[this]`. Conclude with `hd.differentiableAt`.
-/
theorem UpperTheory.Reformulated.B.OneParameterGroupDifferentiableAtZero.main.{u_1} :
    ∀ {W : Type u_1} [inst : NormedAddCommGroup W]
    [inst_1 : NormedSpace ℂ W] [CompleteSpace W] (φ : ℝ → W →L[ℂ] W),
    Continuous φ → φ (0 : ℝ) = (1 : W →L[ℂ] W) → (∀ (s t : ℝ), φ (s + t) = φ s * φ t) → DifferentiableAt ℝ φ (0 : ℝ) := by
  intro W _ _ _ φ hc h0 hmul

  obtain ⟨ε, εpos, hε⟩ := Metric.continuous_iff.mp hc 0 (1/2) (by norm_num)
  set δ : ℝ := ε / 2 with hδ
  have δpos : 0 < δ := by positivity
  set A : W →L[ℂ] W := ∫ s in (0:ℝ)..δ, φ s with hA
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hest : ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ 1/2 * δ := by
    have e1 : A - δ • (1 : W →L[ℂ] W) = ∫ s in (0:ℝ)..δ, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp <;> rfl
    rw [e1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1/2)
      (f := fun s => φ s - 1) (by
        intro x hx
        rw [Set.uIoc_of_le δpos.le] at hx
        have hxd : dist x 0 < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
        have := hε x hxd
        rw [dist_eq_norm, h0] at this
        exact this.le)
    simpa [abs_of_pos δpos] using this
  have hsmall : ‖1 - δ⁻¹ • A‖ < 1 := by
    have : 1 - δ⁻¹ • A = -(δ⁻¹ • (A - δ • (1 : W →L[ℂ] W))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ δpos.ne']; simp
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr δpos)]
    calc δ⁻¹ * ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ δ⁻¹ * (1/2 * δ) :=
          mul_le_mul_of_nonneg_left hest (inv_pos.mpr δpos).le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u := Units.oneSub (1 - δ⁻¹ • A) hsmall
  have hu : (u : W →L[ℂ] W) = δ⁻¹ • A := by simp [u, Units.val_oneSub]
  set B : W →L[ℂ] W := δ⁻¹ • ((u⁻¹ : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)
  have hAB : A * B = 1 := by
    simp only [B, mul_smul_comm, ← smul_mul_assoc, ← hu]
    exact u.mul_inv
  set F : ℝ → W →L[ℂ] W := fun u => ∫ s in (0:ℝ)..u, φ s
  have key : ∀ t, φ t = (F (t + δ) - F t) * B := by
    intro t
    have h1 : φ t * A = F (t + δ) - F t := by
      rw [hA, mul_integral _ _ _ _ (hint 0 δ)]
      have : (fun s => φ t * φ s) = fun s => φ (t + s) := by
        funext s; rw [hmul]
      rw [this, intervalIntegral.integral_comp_add_left (fun s => φ s) t]
      simp only [add_zero, F]
      rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + δ)) (hint 0 t)]
    calc φ t = φ t * A * B := by rw [mul_assoc, hAB, mul_one]
      _ = _ := by rw [h1]
  have hF : ∀ x, HasDerivAt F (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * B) ((φ (0 + δ) - φ 0) * B) 0 := by
    apply HasDerivAt.mul_const
    apply HasDerivAt.sub
    · exact (hF (0 + δ)).comp_add_const 0 δ
    · exact hF 0
  have : φ = fun t => (F (t + δ) - F t) * B := funext key
  rw [this]
  exact hd.differentiableAt
