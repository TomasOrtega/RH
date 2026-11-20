import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_finset_leftTransversal_of_relIndex_ne_zero : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K _ hrel
  have hfin : Finite (H ⧸ K.subgroupOf H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [Subgroup.relIndex, Subgroup.index] using hrel
  let f : H ⧸ K.subgroupOf H → G := fun q => ((Quotient.out q : H) : G)
  have hR : (Set.range f).Finite := Set.finite_range f
  refine ⟨hR.toFinset, ?_, ?_⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hr
    exact (Quotient.out q : H).2
  · intro k hk
    refine ⟨f (QuotientGroup.mk (⟨k, hk⟩ : H)), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact ⟨_, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : H) : H ⧸ K.subgroupOf H)) :
          H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [f] using h1
    · rintro r ⟨hr, hrk⟩
      rw [Set.Finite.mem_toFinset] at hr
      obtain ⟨q, rfl⟩ := hr
      have h2 : (QuotientGroup.mk (Quotient.out q) : H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [f] using hrk
      rw [QuotientGroup.out_eq'] at h2
      simp [f, h2]

end GlobalTheory
