import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BddInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

/- English proof (translation)
Introduce `E _ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous (AdeleBaseChange.adeleMap ℚ E)` using `AdeleBaseChange.continuous_adeleMap`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_map hc`.

Conclude with `Units.continuous_coe_inv.matrix_map hc`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j`. Conclude with `continuous_const`. Conclude with `continuous_const`.

Conclude with `continuous_const`. Conclude with `Units.continuous_val`. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j`. Conclude with `continuous_const`. Conclude with `continuous_const`.

Conclude with `continuous_const`. Conclude with `Units.continuous_coe_inv`. Set `u : ℝ → (TR.Rinf ℚ)ˣ` to `fun t => ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,`. Use function extensionality and compare the values at `fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),`. Use function extensionality and compare the values at `fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩`.

Establish `hu : Continuous u`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_pi fun _ => Real.continuous_exp`. Conclude with `continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)`. Establish `he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t)`.

Use function extensionality and compare the values at `t`. Simplify using `only [iy, dif_neg (Real.exp_ne_zero t)]`. Both sides reduce to the same expression. Rewrite using `[he]`. Conclude with `(TR.continuous_infId ℚ).comp hu`.
-/
theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
