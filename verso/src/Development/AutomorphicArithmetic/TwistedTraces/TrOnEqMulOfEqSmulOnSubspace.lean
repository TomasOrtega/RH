import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Introduce `H _ _ _ W B C c hW h`. Use `haveI := hW`. Establish `hcl : W.topologicalClosure = W` using `(Submodule.closed_of_finiteDimensional W).submodule_topologicalClosure_eq`. Establish `hmem : ∀ x, UpperTheory.ConvolutionTheory.C.prj W x ∈ W`. Introduce `x`.

Establish `hx : UpperTheory.ConvolutionTheory.C.prj W x ∈ W.topologicalClosure`. Simplify using `[UpperTheory.ConvolutionTheory.C.prj]`. Rewrite `hx` using `[hcl]`. Then use the resulting hypothesis. Simplify using `only [UpperTheory.ConvolutionTheory.C.trOn, GroundTheory.Automorphic.trace]`. Rewrite using `[← tsum_mul_left]`.

Use `tsum_congr fun i => ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[h _ (hmem _), map_smul, inner_smul_right]`.
-/
theorem UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (B C : H →L[ℂ] H) (c : ℂ),
        FiniteDimensional ℂ W → (∀ v ∈ W, B v = c • C v) → trOn W B = c * trOn W C := by
  intro H _ _ _ W B C c hW h
  haveI := hW
  have hcl : W.topologicalClosure = W :=
    (Submodule.closed_of_finiteDimensional W).submodule_topologicalClosure_eq
  have hmem : ∀ x, UpperTheory.ConvolutionTheory.C.prj W x ∈ W := by
    intro x
    have hx : UpperTheory.ConvolutionTheory.C.prj W x ∈ W.topologicalClosure := by
      simp [UpperTheory.ConvolutionTheory.C.prj]
    rwa [hcl] at hx
  simp only [UpperTheory.ConvolutionTheory.C.trOn, GroundTheory.Automorphic.trace]
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [h _ (hmem _), map_smul, inner_smul_right]
