import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

open NumberField.mixedEmbedding

private noncomputable def lin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w : InfinitePlace F) (i : Fin 4) : (Fin 4 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
      ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
        ({w : InfinitePlace F // w.IsComplex} → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => mixedSpace F) i)))

end UpperTheory.ConvolutionTheory.R2.Fo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.xEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi F (Fin 4) → (fun v => cw w (v i) * φ v) ∈ schwartzBruhatPi F (Fin 4) := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : (fun v => cw w (v i) * schwartzBruhatTensorPi f g v) =
        schwartzBruhatTensorPi (SchwartzMap.smulLeftCLM ℂ (lin w i) f) g := by
      funext v
      simp only [schwartzBruhatTensorPi]
      rw [SchwartzMap.smulLeftCLM_apply_apply (lin w i).hasTemperateGrowth, smul_eq_mul, mul_assoc]
      congr 1
    rw [e]
    exact schwartzBruhatTensorPi_mem _ hg
  | zero =>
    have e : (fun v => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v
      simp
    rw [e]
    exact zero_mem _
  | add G H _ _ hG hH =>
    have e : (fun v => cw w (v i) * (G + H) v) = (fun v => cw w (v i) * G v) + fun v => cw w (v i) * H v := by
      funext v
      simp [mul_add]
    rw [e]
    exact add_mem hG hH
  | smul c G _ hG =>
    have e : (fun v => cw w (v i) * (c • G) v) = c • fun v => cw w (v i) * G v := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ c hG
