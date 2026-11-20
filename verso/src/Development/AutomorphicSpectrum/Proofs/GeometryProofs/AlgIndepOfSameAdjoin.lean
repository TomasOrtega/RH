import Mathlib

namespace GlobalTheory.CompanionTheory.FieldGen

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
-/
theorem isAlgebraic_adjoin_range_self {k E σ : Type} [Field k] [Field E] [Algebra k E] (y : σ → E) :
    Algebra.IsAlgebraic
      (Algebra.adjoin k (Set.range fun j =>
        (⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ :
          IntermediateField.adjoin k (Set.range y))))
      (IntermediateField.adjoin k (Set.range y)) := by
  set E' := IntermediateField.adjoin k (Set.range y) with hE'
  set y' : σ → E' := fun j => ⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ with hy'
  set A := Algebra.adjoin k (Set.range y') with hA
  have hmap : ∀ p ∈ Algebra.adjoin k (Set.range y), ∃ p' ∈ A, (p' : E) = p := by
    intro p hp
    have h1 : Algebra.adjoin k (Set.range y) = A.map (IntermediateField.val E') := by
      rw [hA, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [h1] at hp
    obtain ⟨p', hp', rfl⟩ := Subalgebra.mem_map.1 hp
    exact ⟨p', hp', rfl⟩
  constructor
  intro z
  obtain ⟨v, hv⟩ := z
  obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.1 hv
  by_cases hq0 : q = 0
  · have hz : (⟨v, hv⟩ : E') = 0 := by
      apply Subtype.ext
      simp [hpq, hq0]
    rw [hz]
    exact isAlgebraic_zero
  obtain ⟨p', hp', hpp⟩ := hmap p hp
  obtain ⟨q', hq', hqq⟩ := hmap q hq
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [← hqq]; rfl)
  refine ⟨Polynomial.C (⟨q', hq'⟩ : A) * Polynomial.X - Polynomial.C ⟨p', hp'⟩, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun f => Polynomial.coeff f 1) h
    simp at h2
    exact hq'0 (congrArg Subtype.val h2 :)
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, sub_eq_zero]
    change q' * (⟨v, hv⟩ : E') = p'
    apply Subtype.ext
    show (q' : E) * v = p'
    rw [hpp, hqq, hpq]
    field_simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem algebraicIndependent_of_adjoin_eq :
    ∀ (K L J : Type) [Field K] [Field L] [Algebra K L] [Finite J] (x y : J → L),
      AlgebraicIndependent K x →
      IntermediateField.adjoin K (Set.range x) = IntermediateField.adjoin K (Set.range y) →
      AlgebraicIndependent K y := by
  intro K L J _ _ _ _ x y hx hxy
  set E := IntermediateField.adjoin K (Set.range y) with hE
  have hal := isAlgebraic_adjoin_range_self (k := K) y
  set y' : J → E := fun j => ⟨y j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩ with hy'
  have hxmem : ∀ j, x j ∈ E := fun j => by
    rw [← hxy]
    exact IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  set x' : J → E := fun j => ⟨x j, hxmem j⟩ with hxd
  have hx' : AlgebraicIndependent K x' := AlgebraicIndependent.of_comp E.val hx
  have hle : Cardinal.mk J ≤ Algebra.trdeg K E := hx'.cardinalMk_le_trdeg
  have htb := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K y' hle
  exact htb.1.map' (f := E.val) E.val.injective

end GlobalTheory.CompanionTheory.FieldGen
