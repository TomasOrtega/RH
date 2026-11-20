import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemOfForall
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem coeffs_mem_maximalIdeal_of_sum_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank) (b : Fin n → R)
    (hb : ∑ j, b j * z j ∈ maximalIdeal R ^ 2) : ∀ j, b j ∈ maximalIdeal R := by
  have h : ∀ k, z k ∈ maximalIdeal R := fun k => hz ▸ Ideal.subset_span ⟨k, rfl⟩
  have h1 : Submodule.span R (Set.range fun k => (⟨z k, h k⟩ : maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hz
  have h2 := IsLocalRing.CotangentSpace.span_image_eq_top_iff.2 h1
  rw [← Set.range_comp] at h2
  have hli := linearIndependent_of_top_le_span_of_card_le_finrank h2.ge (by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; simp [hn])
  have key : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
      = 0 := by
    have h3 : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, b k • (⟨z k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (b k) _
    rw [h3, Ideal.toCotangent_eq_zero]
    simpa using hb
  intro j
  have := Fintype.linearIndependent_iff.1 hli (fun k => residue R (b k)) key j
  exact (residue_eq_zero_iff _).1 this

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_minimal_local_generators :
    ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime],
      ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧
        (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
        h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧
        ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by
  first
  | exact @_root_.GlobalTheory.MultipleMembershipForAll.main
  | exact _root_.GlobalTheory.MultipleMembershipForAll.main
  | (apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultipleMembershipForAll.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultipleMembershipForAll.main ..)

end GlobalTheory
