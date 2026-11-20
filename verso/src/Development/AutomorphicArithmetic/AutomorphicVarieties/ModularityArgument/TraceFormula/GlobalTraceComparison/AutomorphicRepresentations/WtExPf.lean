import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IsDiscreteOfNorm

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

/- English proof (translation)
Introduce `E _ _ _ n π hreg`. Establish `h : ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam)` using `fun φ => by`. Establish `hm : π.HasInfChar φ ((CG.mk π).infChar φ)` using `GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E n (fun τ u o => GlobalTheory.SpehInfChar.cap_commute_act τ u o) (CG.mk π) φ`. Take `⟨lam, hl⟩` from `DiscreteGroups.T1.G.reg_of hreg hm`. Conclude with `⟨lam, hl ▸ hm⟩`.

Use `choose lamE hlam using h`. Conclude with `⟨lamE, hlam⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtEx_pf :
    WtEx := by
  intro E _ _ _ n π hreg
  have h : ∀ φ : E →+* ℂ, ∃ lam : DomWeight n, π.HasInfChar φ (infOfWeight lam) := fun φ => by
    have hm : π.HasInfChar φ ((CG.mk π).infChar φ) :=
      GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E n (fun τ u o => GlobalTheory.SpehInfChar.cap_commute_act τ u o) (CG.mk π) φ
    obtain ⟨lam, hl⟩ := DiscreteGroups.T1.G.reg_of hreg hm
    exact ⟨lam, hl ▸ hm⟩
  choose lamE hlam using h
  exact ⟨lamE, hlam⟩
