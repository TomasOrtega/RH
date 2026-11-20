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
Use `ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_` and prove the remaining obligations. Conclude with `Lp.ext ((h f i).trans (h' f i).symm)`.
-/
private theorem op_unique {D : Dom E n 0} {Φ : Matrix ι ι (H E n 0 → ℂ)}
    {T T' : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (h : IsROp D Φ T) (h' : IsROp D Φ T') : T = T' := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun i => ?_
  exact Lp.ext ((h f i).trans (h' f i).symm)

/- English proof (translation)
Introduce `i j`. Use `⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩` and prove the remaining obligations. Establish `h` using `(hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))`. Conclude with `h.comp_left (g := starRingEnd ℂ) (map_zero _)`.
-/
private theorem isTestM_adjM {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((hΦ j i).1.comp continuous_inv), ?_⟩
  have h := (hΦ j i).2.comp_homeomorph (Homeomorph.inv (H E n 0))
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `E _ _ _ n hn D π hfix ι _ Φ T hΦ hT f`. Take `⟨T₀, h₀, hadj, -⟩` from `PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D ι Φ hΦ`. Take `rfl : T₀ = T` from `op_unique h₀ hT`. Establish `hS : ∀ g ∈ piSp D π ι, T₀ g ∈ piSp D π ι` using `piInv E n hn D π hfix ι Φ T₀ hΦ hT`. Establish `hS' : ∀ g ∈ piSp D π ι, ContinuousLinearMap.adjoint T₀ g ∈ piSp D π ι` using `piInv E n hn D π hfix ι (adjM Φ) _ (isTestM_adjM hΦ) hadj`.

Establish `hO : ∀ g ∈ (piSp D π ι)ᗮ, T₀ g ∈ (piSp D π ι)ᗮ`. Introduce `g hg`. Rewrite `hg`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left]`.

Conclude with `hg _ (hS' u hu)`. Use `Submodule.eq_starProjection_of_mem_orthogonal (hS _ (Submodule.starProjection_apply_mem _ _)) ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `hO _ (Submodule.sub_starProjection_mem_orthogonal _)`.
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
