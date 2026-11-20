import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace AddBlockData

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chartPow_ne_zero {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
theorem elt_div_elt {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (i j : Fin (D.size + 1)) :
    D.elt i / D.elt j = D.xi c i * (D.xi c j)⁻¹ := by
  have hp := chartPow_ne_zero hc D.deg
  simp only [xi]
  field_simp

end AddBlockData

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem ChartRingDescription.proof : ChartRingDescription.Statement := by
  intro ι _ _ n P D c hc j hj
  have hp := AddBlockData.chartPow_ne_zero hc D.deg
  set S := Subring.closure (insert (D.xi c j)⁻¹ (P.chartRing c : Set P.FunField))
  have hA : (P.chartRing c : Set P.FunField) ⊆ S := fun x hx ↦
    Subring.subset_closure (Set.mem_insert_of_mem _ hx)
  have hinv : (D.xi c j)⁻¹ ∈ S := Subring.subset_closure (Set.mem_insert _ _)
  apply le_antisymm
  · rw [AddBlockData.extChartRing, Subring.closure_le]
    rintro x (⟨v, rfl⟩ | ⟨i, rfl⟩)
    · exact hA (Subring.subset_closure ⟨v, rfl⟩)
    · show D.elt i / D.elt j ∈ S
      rw [D.elt_div_elt hc i j]
      exact S.mul_mem (hA (D.chart_mem c hc i)) hinv
  · have hA' : P.chartRing c ≤ D.extChartRing c j := by
      rw [ArithVariety.chartRing]
      exact Subring.closure_mono Set.subset_union_left
    rw [Subring.closure_le]
    rintro x (rfl | hx)
    · obtain ⟨u, hu, hsum⟩ := D.generating c hc
      have h : (D.xi c j)⁻¹ = ∑ i, u i * (D.elt i / D.elt j) := by
        rw [← one_mul (D.xi c j)⁻¹, ← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [D.elt_div_elt hc i j, mul_assoc]
        rfl
      rw [h]
      refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hA' (hu i)) ?_
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
    · exact hA' hx

end

end GroundTheory.Heights₂.Heights
