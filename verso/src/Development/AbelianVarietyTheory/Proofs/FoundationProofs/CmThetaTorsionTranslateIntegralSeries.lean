import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLawStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanishStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem intMv_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) : IntegralMv f ↔ GlobalTheory.EvenTheta.IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Combine the linear equalities and inequalities to obtain the conclusion.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem transl_holds : ∀ D : D7, GL3Theta.transl D := by
  intro D p _ cc δ g hg t ht
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg'
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, -, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  rw [← hΛ] at hlat huse
  have hlat' : GlobalTheory.EvenTheta.IsLat g.abelian₂ := hlat
  have hred := GlobalTheory.T.torsionPoint_padicAbscissa_norm_le_one D p cc δ g hg
  have hun := GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series D p cc δ g hg hred
  obtain ⟨n, hn, hnp, hnt⟩ := ht.2
  have hM : logc g t = 0 := by
    refine GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish g.abelian₂ hlat' n hn (logc g) (fun s hs => by simp [logc, hs]) ?_ ?_ t hnt
    · intro s ω hs hω
      by_cases h1 : s ∈ g.abelian₂
      · simp [logc, h1, add_mem h1 hω]
      · have h2 : s + ω ∉ g.abelian₂ := fun h => h1 (by simpa using sub_mem h hω)
        simp only [logc, h1, h2, if_false]
        rw [GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic D p cc δ g hg s ω ⟨n, hn, hs⟩ hω]
    · intro P Q hP hQ hQ'
      exact GlobalTheory.T.thetaTranslateLogNorm_parallelogram_law D p cc δ g hg hred hun P Q ⟨n, hn, hnp, hP⟩ ⟨hQ', n, hn, hnp, hQ⟩
  have hA : GlobalTheory.EvenTheta.AlgEnt (U1 g.abelian₂ t (sgStar g.abelian₂)) := ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse t ⟨n, hn, hnt⟩⟩
  obtain ⟨hq, hc0⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ hA
  have hne : U1 g.abelian₂ t (sgStar g.abelian₂) 0 ≠ 0 := by
    simp only [U1, zero_add, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
    exact fun h => ht.1 ((hlat'.sg_eq_zero t).1 h)
  have hcne : cval g t ≠ 0 := by
    unfold cval lamC
    rw [dif_pos hq]
    exact (map_ne_zero g.lam).2 fun h => hne (congrArg Subtype.val h)
  have hc1 : ‖cval g t‖ = 1 := by
    simp only [logc, ht.1, if_false] at hM
    rcases Real.log_eq_zero.1 hM with h | h | h
    · exact absurd (norm_eq_zero.1 h) hcne
    · exact h
    · linarith [norm_nonneg (cval g t)]
  obtain ⟨w, hw, -, hτ⟩ := hun t ht
  refine ⟨?_, ?_⟩
  · rw [intMv_iff]
    change GlobalTheory.EvenTheta.IntSer (tau g t)
    intro k
    rw [hτ, PowerSeries.coeff_C_mul, norm_mul, hc1, one_mul]
    exact hw k
  · rw [hc0]; exact hc1

end GlobalTheory.ThetaTransl
