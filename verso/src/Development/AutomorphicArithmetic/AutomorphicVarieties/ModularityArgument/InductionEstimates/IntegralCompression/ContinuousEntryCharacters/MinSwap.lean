import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.SingleShift
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minSwap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ τ₁ τ₂ : Submodule ℂ (LL μ),
        τ₁.map (θ.U : LL μ →ₗ[ℂ] LL μ) = τ₂ → ∀ s u n q, CE.MinAt μ τ₁ (s, u) n q → CE.MinAt μ τ₂ (s + 1, u) n q := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ τ₁ τ₂ hτ s u n q hmin
  obtain ⟨hnorm, -, hint⟩ := UpperTheory.ConvolutionTheory.Dp.twUnitary E 2 μ θ
  have htw := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw F E σ D CF CE hC μ θ hθ
  let L : LL μ →ₗᵢ[ℂ] LL μ := ⟨(θ.U : LL μ →ₗ[ℂ] LL μ), hnorm⟩
  have hL : ∀ v, L v = θ.U v := fun _ => rfl
  have key : ∀ n' q' v, θ.U (CE.Pi μ (s, u) n' q' v) = CE.Pi μ (s + 1, u) n' q' (θ.U v) := by
    intro n' q' v
    unfold Co.Pi
    rw [← hL, ← L.integral_comp_comm]
    congr 1
    funext m
    rw [map_smul, hL, hint, htw]
  subst hτ
  obtain ⟨⟨v, hv, hne⟩, hz⟩ := hmin
  refine ⟨⟨θ.U v, Submodule.mem_map_of_mem hv, fun h => hne ?_⟩, ?_⟩
  · rw [← key] at h
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  · rintro n' q' hn _ ⟨w, hw, rfl⟩
    have := key n' q' w
    rw [hz n' q' hn w hw, map_zero] at this
    exact this.symm
