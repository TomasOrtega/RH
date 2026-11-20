import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
