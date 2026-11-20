import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseLift
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem denseBoundedHeight : DenseBoundedHeight.Statement := by
  intro ι _ _ n P
  obtain ⟨c, hc⟩ := P.exists_chart
  obtain ⟨s, g0, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (P.ChartAlg c)
  let b : Coord n → P.ChartAlg c := fun v ↦ (P.chartMap c).rangeRestrict (X v)
  choose δ R hδ hR hbd using fun v ↦ exists_integral_bound g0 hint (b v)
  set Δ : ℕ := ∏ v, δ v with hΔ
  set R0 : ℝ := 1 + ∑ v, R v with hR0
  have hΔpos : 0 < Δ := Finset.prod_pos fun v _ ↦ hδ v
  have hRnn : ∀ v, 0 ≤ R v := fun v ↦ zero_le_one.trans (hR v)
  have hR0pos : 0 < R0 := by
    have := Finset.sum_nonneg fun v (_ : v ∈ Finset.univ) ↦ hRnn v
    linarith
  refine ⟨{z | ∃ ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (X j)) ^ N = 1) ∧ z = P.chartPoint c ψ},
    ∑ k, (Real.log Δ + Real.log (Real.sqrt (n k + 1) * R0)), ?_, ?_, ?_⟩
  · rintro z ⟨ψ, -, rfl⟩
    exact P.chartPoint_mem c hc ψ
  · intro m f hf hvan
    by_contra hfP
    have hg := P.chartMap_ne_zero c hc hf hfP
    obtain ⟨ψ, hψ, hroots⟩ := exists_algHom_rootsOfUnity_ne_zero g0 hinj hint hg
    apply hψ
    rw [← P.evalCone_chartPoint c ψ f]
    exact hvan _ ⟨ψ, hroots, rfl⟩
  · rintro z ⟨ψ, hroots, rfl⟩
    refine height_standard_le _ (P.chartPoint_mem c hc ψ).1 hΔpos hR0pos (fun k i ↦ ?_)
      (fun σ k i ↦ ?_)
    · have h1 := (hbd ⟨k, i⟩ ψ hroots).1
      have h2 : (Δ : AlgebraicClosure ℚ) * P.chartPoint c ψ k i =
          ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ) *
            ((δ ⟨k, i⟩ : AlgebraicClosure ℚ) * ψ (b ⟨k, i⟩)) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
        rfl
      rw [h2]
      have h3 : IsIntegral ℤ (((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : AlgebraicClosure ℚ)) := by
        have := isIntegral_algebraMap (R := ℤ) (A := AlgebraicClosure ℚ)
          (x := ((∏ w ∈ Finset.univ.erase ⟨k, i⟩, δ w : ℕ) : ℤ))
        simpa using this
      exact h3.mul h1
    · calc ‖σ (P.chartPoint c ψ k i)‖ ≤ R ⟨k, i⟩ := (hbd ⟨k, i⟩ ψ hroots).2 σ
        _ ≤ ∑ v, R v := Finset.single_le_sum (fun v _ ↦ hRnn v) (Finset.mem_univ _)
        _ ≤ R0 := by linarith

end

end GroundTheory.Heights₂.Heights
