import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology

namespace GlobalTheory.JSW

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_charAnnihilator_of_mem_nhds_zero {F : Type} [NormedField F] [ProperSpace F] (ψ : AddChar F ℂ)
    (hlc : IsLocallyConstant ψ) (hψ : ψ ≠ 1) {ι : Type} [Fintype ι] (L : Set (ι → F))
    (hL : L ∈ nhds (0 : ι → F)) :
    IsCompact {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hL
  have hcont : Continuous (fun x : F => ψ x) := hlc.continuous
  have hclosed : IsClosed {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
    have : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} = ⋂ y ∈ L, {r : ι → F | ψ (r ⬝ᵥ y) = 1} := by
      ext r; simp
    rw [this]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    refine hcont.comp ?_
    simp only [dotProduct]
    fun_prop
  have hR : 0 ≤ ‖t‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hsub : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} ⊆ Metric.closedBall 0 (‖t‖ / ε) := by
    intro r hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    by_contra hlt
    push_neg at hlt
    have hri : r i ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hlt; linarith
    have hpos : 0 < ‖r i‖ := norm_pos_iff.2 hri
    have hy : Pi.single i (t / r i) ∈ L := by
      apply hball
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, norm_div, div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hε] at hlt
        linarith
      · rw [Pi.single_eq_of_ne hj, norm_zero]; exact hε
    have := hr _ hy
    rw [dotProduct_single, mul_div_cancel₀ _ hri] at this
    exact ht this
  exact (isCompact_closedBall 0 (‖t‖ / ε)).of_isClosed_subset hclosed hsub

end GlobalTheory.JSW
