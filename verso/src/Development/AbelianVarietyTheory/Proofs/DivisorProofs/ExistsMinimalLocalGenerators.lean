import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemOfForall
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `h : ∀ k, z k ∈ maximalIdeal R` using `fun k => hz ▸ Ideal.subset_span ⟨k, rfl⟩`. Establish `h1 : Submodule.span R (Set.range fun k => (⟨z k, h k⟩ : maximalIdeal R)) = ⊤`. Apply `Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Conclude with `hz`.

Establish `h2` using `IsLocalRing.CotangentSpace.span_image_eq_top_iff.2 h1`. Rewrite `h2` using `[← Set.range_comp]`. Establish `hli` using `linearIndependent_of_top_le_span_of_card_le_finrank h2.ge (by`. Rewrite using `[← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Simplify using `[hn])`.

Establish `key : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R) = 0`. Establish `h3 : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R) = (maximalIdeal R).toCotangent (∑ k, b k • (⟨z k, h k⟩ : maximalIdeal R))`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Conclude with `algebraMap_smul (ResidueField R) (b k) _`. Rewrite using `[h3, Ideal.toCotangent_eq_zero]`. Simplify using `using hb`. Introduce `j`. Use `Fintype.linearIndependent_iff.1 hli (fun k => residue R (b k)) key j` as an intermediate fact.

Conclude with `(residue_eq_zero_iff _).1 this`.
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
Use `first`. Consider the case `exact @_root_.GlobalTheory.MultipleMembershipForAll.main`. Consider the case `exact _root_.GlobalTheory.MultipleMembershipForAll.main`. Consider the case `(apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.MultipleMembershipForAll.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.MultipleMembershipForAll.main ..)`.
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
