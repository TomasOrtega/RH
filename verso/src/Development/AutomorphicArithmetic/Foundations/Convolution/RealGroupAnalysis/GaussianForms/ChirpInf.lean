import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

/- English proof (translation)
Introduce `K ι _ _ _ p l`. Establish `hp : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => MvPolynomial.eval x p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `using Function.HasTemperateGrowth.const (E := ι → mixedEmbedding.mixedSpace K) a`.

Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Conclude with `hp.fun_add hq`. Consider the case `mul_X p i hp`. Establish `hi : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => x i` using `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => mixedEmbedding.mixedSpace K) i).hasTemperateGrowth`.

Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.fun_mul hi`. Conclude with `GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (l.hasTemperateGrowth.comp hp)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.chirpInf :
    ∀ (K ι : Type) [Field K] [NumberField K] [Fintype ι] (p : MvPolynomial ι (mixedEmbedding.mixedSpace K)) (l : mixedEmbedding.mixedSpace K →L[ℝ] ℝ),
    Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => ((Real.fourierChar (l (MvPolynomial.eval x p)) : Circle) : ℂ) := by
  intro K ι _ _ _ p l
  have hp : Function.HasTemperateGrowth
      fun x : ι → mixedEmbedding.mixedSpace K => MvPolynomial.eval x p := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa using Function.HasTemperateGrowth.const (E := ι → mixedEmbedding.mixedSpace K) a
    | add p q hp hq =>
      simp only [map_add]
      exact hp.fun_add hq
    | mul_X p i hp =>
      have hi : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => x i :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => mixedEmbedding.mixedSpace K)
          i).hasTemperateGrowth
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.fun_mul hi
  exact GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (l.hasTemperateGrowth.comp hp)
