import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Put the expressions in a common number system so they can be compared. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exists_systemOfParameters_insert (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (a : S) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧
      ringKrullDim S = (n : WithBot ℕ∞) + 1 ∧
      ∃ N : ℕ, maximalIdeal S ^ N ≤ Ideal.span (insert a (Set.range x)) := by
  classical
  have hIle : Ideal.span {a} ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).mpr ha
  have hIne : Ideal.span {a} ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hIle))
  have : Nontrivial (S ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (S ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (S ⧸ Ideal.span {a}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha0) ha
  obtain ⟨s, hsmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ Ideal.span {a}))
  have hht := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S ⧸ Ideal.span {a})
  have hsle : Ideal.span (s : Set (S ⧸ Ideal.span {a})) ≤ maximalIdeal (S ⧸ Ideal.span {a}) :=
    hsmin.1.2
  have hcomap : (maximalIdeal (S ⧸ Ideal.span {a})).comap (Ideal.Quotient.mk (Ideal.span {a})) =
      maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmapeq : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (maximalIdeal S) =
      maximalIdeal (S ⧸ Ideal.span {a}) := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  let e := s.equivFin
  let x : Fin s.card → S := fun i =>
    (Ideal.Quotient.mk_surjective ((e.symm i : S ⧸ Ideal.span {a}))).choose
  have hx : ∀ i, Ideal.Quotient.mk (Ideal.span {a}) (x i) = e.symm i := fun i =>
    (Ideal.Quotient.mk_surjective _).choose_spec
  have hrange : Ideal.Quotient.mk (Ideal.span {a}) '' Set.range x =
      (s : Set (S ⧸ Ideal.span {a})) := by
    rw [← Set.range_comp]
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      simp only [Function.comp_apply, hx]
      exact (e.symm i).2
    · intro hq
      exact ⟨e ⟨q, hq⟩, by simp [hx]⟩
  refine ⟨s.card, x, fun i => ?_, ?_, ?_⟩
  · rw [← hcomap, Ideal.mem_comap, hx]
    exact hsle (Ideal.subset_span (e.symm i).2)
  · rw [← hdim, ← hht, ← hcard]
    norm_cast
  · have hrad : maximalIdeal (S ⧸ Ideal.span {a}) ≤
        (Ideal.span (s : Set (S ⧸ Ideal.span {a}))).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro p ⟨hsp, hp⟩
      exact hsmin.2 ⟨hp, hsp⟩ (IsLocalRing.le_maximalIdeal hp.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨N, fun y hy => ?_⟩
    have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) hy
    rw [Ideal.map_pow, hmapeq] at h1
    have h2 := hN h1
    rw [← hrange, ← Ideal.map_span] at h2
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hzy)
    exact Ideal.mem_span_insert.mpr ⟨-c, z, hz, by linear_combination hc⟩

end GlobalTheory
