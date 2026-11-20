import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `K _ _ n r w i y x`. Establish `key : ∀ v, v ∉ Set.range w → finAt v (finEmb K n (AdelicGLn.localEmbedding (w i) y * x)) = finAt v (finEmb K n x)`. Introduce `v hv`. Establish `hne : v ≠ w i` using `fun h => hv ⟨i, h.symm⟩`. Establish `h1` using `(UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 v hne y`.

Establish `e : ∀ z : AdelicGLn.FiniteAdelicGL K n, finAt v (finEmb K n z) = AdelicGLn.finiteRestrictedEquiv K n z v` using `fun z => rfl`. Rewrite `h1` using `[e]`. Rewrite using `[e, e, map_mul, RestrictedProduct.mul_apply, h1, one_mul]`. Establish `hmem : (AdelicGLn.localEmbedding (w i) y * x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) ↔ (x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompleti …`. Simplify using `only [Set.mem_setOf_eq]`.

Conclude with `forall₂_congr fun v hv => by rw [key v hv]`. Distinguish the cases in `hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]`.
-/
theorem UpperTheory.indicator_integral_away_mul_localEmbedding :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (i : Fin r) (y : Gw n (w i)) (x : AdelicGLn.FiniteAdelicGL K n),
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) (AdelicGLn.localEmbedding (w i) y * x) =
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x := by
  intro K _ _ n r w i y x
  have key : ∀ v, v ∉ Set.range w →
      finAt v (finEmb K n (AdelicGLn.localEmbedding (w i) y * x)) = finAt v (finEmb K n x) := by
    intro v hv
    have hne : v ≠ w i := fun h => hv ⟨i, h.symm⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 v hne y
    have e : ∀ z : AdelicGLn.FiniteAdelicGL K n,
        finAt v (finEmb K n z) = AdelicGLn.finiteRestrictedEquiv K n z v := fun z => rfl
    rw [e] at h1
    rw [e, e, map_mul, RestrictedProduct.mul_apply, h1, one_mul]
  have hmem : (AdelicGLn.localEmbedding (w i) y * x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) ↔
      (x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) := by
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun v hv => by rw [key v hv]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
