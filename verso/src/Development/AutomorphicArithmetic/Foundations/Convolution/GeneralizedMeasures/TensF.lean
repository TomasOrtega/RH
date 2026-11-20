import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.GM.avgF :
    AvgF := by
  intro F _ _ n hn S β f hS hoff
  obtain ⟨r, w, hw, hr⟩ : ∃ (r : ℕ) (w : Fin r → Pl F), Function.Injective w ∧ Set.range w = (S : Set (Pl F)) :=
    ⟨S.card, fun i => (S.equivFin.symm i : Pl F),
      Subtype.val_injective.comp S.equivFin.symm.injective, by
        ext v
        constructor
        · rintro ⟨i, rfl⟩
          exact (S.equivFin.symm i).2
        · intro hv
          exact ⟨S.equivFin ⟨v, hv⟩, by simp⟩⟩
  have ht : ∀ i, C.Test (f (w i)) := fun i => hS _ (by
    have : w i ∈ (S : Set (Pl F)) := hr ▸ Set.mem_range_self i
    exact this)
  have ho : ∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set (C.Gw n v)).indicator 1 := by
    intro v hv
    exact hoff v (fun h => hv (hr ▸ h))
  obtain ⟨e, he, ⟨U, hUo, hU⟩, -⟩ := UpperTheory.ConvolutionTheory.Tf.finTens F n (Measure.haar) (Measure.haar) r w hw f ht ho
  refine ⟨e, ?_, fun x => he x, fun x => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hc : Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
      have : Continuous (fun y : AdelicGLn.FiniteAdelicGL F n => x⁻¹ * y) := continuous_const.mul continuous_id
      simpa using this.tendsto x
    filter_upwards [hc (hUo.mem_nhds U.one_mem)] with y hy
    have := (hU _ hy x).2
    simpa using this
  · obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.Tf.avgTens F n hn β e (fun g => β (infPart F n g) * e (finPart F n g)) (fun _ => rfl)
    have hΦ : tensF (onInf β) f = fun g => β (infPart F n g) * e (finPart F n g) := by
      funext g
      simp only [tensF, onInf]
      rw [h2 g, he (finPart F n g)]
      congr 1
    rw [hΦ, h1 x]
