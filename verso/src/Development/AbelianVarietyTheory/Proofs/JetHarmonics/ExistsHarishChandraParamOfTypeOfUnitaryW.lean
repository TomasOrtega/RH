import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepUStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem besType_continuous_blockW (k r : ℕ) : Continuous (PI.UpqRep.blockW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold PI.UpqRep.blockW
  split_ifs
  · exact continuous_apply_apply _ _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem besType_hcParam : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Q.IsType k r z π u → ∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π := by
  intro k r Wp _ _ _ z π u hz hT hπ
  obtain ⟨g, hg, hin, honto⟩ := GlobalTheory.T.exists_frame_conj_unitaryBlock_eq_unitaryComplement k r z hz hT
  obtain ⟨hnt, ⟨h1, hmul⟩, hcont, hnorm, hirr, -⟩ := hπ
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hc : Continuous (fun x : Matrix (Fin k) (Fin k) ℂ => g * PI.UpqRep.blockW k r x * g⁻¹) :=
    (continuous_const.matrix_mul (besType_continuous_blockW k r)).matrix_mul continuous_const
  haveI := hnt
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_highestWeight_irreducible_unitaryRep_U k Wp (fun x => π (g * PI.UpqRep.blockW k r x * g⁻¹))
    (by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show π (g * PI.UpqRep.blockW k r 1 * g⁻¹) = 1
        rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
        exact h1
      · intro x hx y hy
        have e : g * PI.UpqRep.blockW k r (x * y) * g⁻¹ =
            g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) := by
          rw [← PI.HwUniqW.blockW_mul]
          calc g * (PI.UpqRep.blockW k r x * PI.UpqRep.blockW k r y) * g⁻¹
              = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
                rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
        show π (g * PI.UpqRep.blockW k r (x * y) * g⁻¹) = _
        rw [e]
        exact hmul _ (hin x hx) _ (hin y hy)
      · intro x hx v
        exact hnorm _ (hin x hx) v
      · intro v
        have h2 : ContinuousOn (fun x : Matrix (Fin k) (Fin k) ℂ => π (g * PI.UpqRep.blockW k r x * g⁻¹))
            (PI.UpqRep.UJset (PI.UpqRep.allPos k)) :=
          hcont.comp hc.continuousOn (fun x hx => hin x hx)
        exact h2.clm_apply continuousOn_const)
    (by
      intro S hS
      refine hirr S ?_
      intro h hh v hv
      obtain ⟨x, hx, rfl⟩ := honto h hh
      exact hS x hx v hv)
  exact ⟨u₀, g, hg, hu₀⟩

end GlobalTheory
