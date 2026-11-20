import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Use `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`. Establish `hc : Continuous (NormedSpace.exp : A → A)` using `NormedSpace.exp_continuous`. Use `set f : ℝ → ℝ → A := fun t s => NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • (X + t • V)) with hf`. Establish `hfc : Continuous (Function.uncurry f)`. Simplify using `only [hf, Function.uncurry_def]`.

Conclude with `((hc.comp (by fun_prop)).mul continuous_const).mul (hc.comp (by fun_prop))`. Use `set F : ℝ → A := fun t => ∫ s in (0 : ℝ)..1, f t s with hF`. Establish `hFc : Continuous F` using `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 1`. Establish `key : ∀ t : ℝ, NormedSpace.exp (X + t • V) = NormedSpace.exp X + t • F t`. Introduce `t`.

Establish `hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • X) * NormedSpace.exp (s • (X + t • V))) (t • f t s) s`. Introduce `s`. Establish `h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s`. Simplify using `using (hasDerivAt_id s).const_sub 1`. Establish `h1` using `(hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - s)).scomp s h0`.

Establish `h2` using `hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + t • V) s`. Establish `h3` using `h1.mul h2`. Use `h3.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [hf, Function.comp_apply, neg_smul, one_smul, add_mul, mul_add, mul_assoc, neg_mul, smul_mul_assoc, mul_smul_comm]`. Normalize the expressions using the abelian group laws.

Establish `hi : IntervalIntegrable (fun s => t • f t s) volume 0 1` using `((hfc.comp (Continuous.prodMk_right t)).const_smul t).intervalIntegrable 0 1`. Establish `h` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi`. Rewrite `h` using `[intervalIntegral.integral_smul]`. Simplify using `only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, one_smul, sub_zero, mul_one] at h`. Simplify using `only [hF]`.

Rewrite using `[h]`. Normalize the expressions using the abelian group laws. Establish `hF0 : F 0 = ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X)`. Simplify using `[hF, hf]`. Rewrite using `[← hF0, hasDerivAt_iff_tendsto_slope_zero]`.

Establish `ht : Filter.Tendsto F (nhdsWithin 0 {0}ᶜ) (nhds (F 0))` using `hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Use `ht.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with t ht0`. Establish `ht0' : t ≠ 0` using `ht0`. Rewrite using `[key (0 + t), key 0]`.

Simplify using `[smul_smul, inv_mul_cancel₀ ht0']`.
-/
theorem hasDerivAt_exp_add_smul_duhamel (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X V : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (X + t • V))
      (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X)) 0 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Continuous (NormedSpace.exp : A → A) := NormedSpace.exp_continuous
  set f : ℝ → ℝ → A := fun t s =>
    NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • (X + t • V)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    exact ((hc.comp (by fun_prop)).mul continuous_const).mul (hc.comp (by fun_prop))
  set F : ℝ → A := fun t => ∫ s in (0 : ℝ)..1, f t s with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 1
  have key : ∀ t : ℝ, NormedSpace.exp (X + t • V) = NormedSpace.exp X + t • F t := by
    intro t
    have hd : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => NormedSpace.exp ((1 - s) • X) * NormedSpace.exp (s • (X + t • V)))
        (t • f t s) s := by
      intro s
      have h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub 1
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - s)).scomp s h0
      have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + t • V) s
      have h3 := h1.mul h2
      refine h3.congr_deriv ?_
      simp only [hf, Function.comp_apply, neg_smul, one_smul, add_mul, mul_add, mul_assoc,
        neg_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have hi : IntervalIntegrable (fun s => t • f t s) volume 0 1 :=
      ((hfc.comp (Continuous.prodMk_right t)).const_smul t).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
    rw [intervalIntegral.integral_smul] at h
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, one_smul, sub_zero,
      mul_one] at h
    simp only [hF]
    rw [h]
    abel
  have hF0 : F 0 = ∫ s in (0 : ℝ)..1,
      NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X) := by
    simp [hF, hf]
  rw [← hF0, hasDerivAt_iff_tendsto_slope_zero]
  have ht : Filter.Tendsto F (nhdsWithin 0 {0}ᶜ) (nhds (F 0)) :=
    hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : t ≠ 0 := ht0
  rw [key (0 + t), key 0]
  simp [smul_smul, inv_mul_cancel₀ ht0']

end GlobalTheory
