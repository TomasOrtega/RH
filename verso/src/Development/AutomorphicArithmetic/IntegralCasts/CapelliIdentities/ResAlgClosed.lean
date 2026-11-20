import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
