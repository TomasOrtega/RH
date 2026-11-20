import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

/- English proof (translation)
Introduce `E _ _ _ n μ π φ t t' h₁ h₂`. Take `⟨L₁, e₁, -, rfl⟩` from `h₁`. Take `⟨L₂, e₂, -, rfl⟩` from `h₂`. Choose the witnesses or unpack the hypotheses as in `rfl : L₁ = L₂ := by`. Use `LinearMap.ext fun ψ => Subtype.ext (Subtype.ext (funext fun x => ?_))` and prove the remaining obligations.

Rewrite using `[e₁ ψ x, e₂ ψ x]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twUniq_pf :
    TwUniq := by
  intro E _ _ _ n μ π φ t t' h₁ h₂
  obtain ⟨L₁, e₁, -, rfl⟩ := h₁
  obtain ⟨L₂, e₂, -, rfl⟩ := h₂
  obtain rfl : L₁ = L₂ := by
    refine LinearMap.ext fun ψ => Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [e₁ ψ x, e₂ ψ x]
  rfl
