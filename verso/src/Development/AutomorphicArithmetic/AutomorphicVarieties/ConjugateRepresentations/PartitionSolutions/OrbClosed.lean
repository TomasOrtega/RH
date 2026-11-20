import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts

open UpperTheory.V.Cj.A

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.A.orbClosed :
    OrbClosed := by
  intro Γ V S _ _ _ _ d G hG K hKY hK s s'
  unfold UpperTheory.V.Lit.Dr.Geo.Proper at hG
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hpY, hpA⟩
  obtain ⟨L, hLn, hLY, hL⟩ := local_compact_nhds (G.isOpen.mem_nhds hpY)
  have hFfin : {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K}.Finite :=
    hG (L ∪ K) (Set.union_subset hLY hKY) (hL.union hK) s s'
  set F := {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K} with hF
  have hBc : IsClosed (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K) :=
    hFfin.isClosed_biUnion fun γ _ => hK.isClosed.preimage (G.ρ γ).continuous
  have hpB : p ∉ ⋃ γ ∈ F, (G.ρ γ) ⁻¹' K := by
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists]
    intro γ hγF hγ
    exact hpA ⟨γ, hγF.1, hγ⟩
  have hnb : (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K)ᶜ ∈ nhds p := hBc.isOpen_compl.mem_nhds hpB
  filter_upwards [hLn, hnb] with q hqL hqB
  refine ⟨hLY hqL, ?_⟩
  rintro ⟨γ, hσ, hγ⟩
  apply hqB
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨γ, ⟨hσ, q, Or.inl hqL, Or.inr hγ⟩, hγ⟩
