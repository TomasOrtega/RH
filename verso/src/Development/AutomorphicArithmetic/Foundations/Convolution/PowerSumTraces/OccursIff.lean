import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.C.occursIff :
    UpperTheory.ConvolutionTheory.C.OccursIff := by
  intro K _ _ n μ _ V hV w σ
  constructor
  · rintro ⟨f, hf0, hfV, hf⟩
    refine ⟨f.codRestrict V hfV, ?_, ?_⟩
    · intro h
      apply hf0
      ext1 x
      have := congrArg (fun l : σ.V →ₗ[ℂ] V => ((l x : V) : LL μ)) h
      simpa using this
    · intro g x
      apply Subtype.ext
      have h1 := hf g x
      rw [UpperTheory.ConvolutionTheory.Dp.rhoLoc K n μ w g (f x)] at h1
      exact h1
  · rintro ⟨f, hf0, hf⟩
    refine ⟨V.subtype ∘ₗ f, ?_, fun x => (f x).2, ?_⟩
    · intro h
      apply hf0
      ext1 x
      apply Subtype.ext
      have := congrArg (fun l : σ.V →ₗ[ℂ] LL μ => l x) h
      simpa using this
    · intro g x
      have h1 := congrArg (Subtype.val) (hf g x)
      rw [UpperTheory.ConvolutionTheory.Dp.rhoLoc K n μ w g]
      exact h1
