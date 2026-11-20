import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem op_unique {D : Dom E n 0} {Φ : Matrix ι ι (H E n 0 → ℂ)}
    {T T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (h : IsROp D Φ T) (h' : IsROp D Φ T') : T = T' := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_
  exact Lp.ext ((h f i).trans (h' f i).symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem isTestM_adjM {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩
  have h := (hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pComm_pf :
    PComm := by
  intro E _ _ _ n hn D π hfix ι _ Φ T hΦ hT f
  obtain ⟨T₀, h₀, hadj, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D ι Φ hΦ
  obtain rfl : T₀ = T := op_unique h₀ hT
  have hS : ∀ g ∈ piSp D π ι, T₀ g ∈ piSp D π ι := piInv E n hn D π hfix ι Φ T₀ hΦ hT
  have hS' : ∀ g ∈ piSp D π ι, ContinuousLinearMap.adjoint T₀ g ∈ piSp D π ι :=
    piInv E n hn D π hfix ι (adjM Φ) _ (isTestM_adjM hΦ) hadj
  have hO : ∀ g ∈ (piSp D π ι)ᗮ, T₀ g ∈ (piSp D π ι)ᗮ := by
    intro g hg
    rw [Submodule.mem_orthogonal] at hg ⊢
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact hg _ (hS' u hu)
  refine Submodule.eq_starProjection_of_mem_orthogonal (hS _ (Submodule.starProjection_apply_mem _ _)) ?_
  rw [← map_sub]
  exact hO _ (Submodule.sub_starProjection_mem_orthogonal _)
