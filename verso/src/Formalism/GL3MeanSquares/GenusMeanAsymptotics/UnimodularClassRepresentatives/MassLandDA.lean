import Mathlib

open Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadAdj

variable {F : Type*} [Field F] (c : F)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem monic_pol : (X ^ 2 - C c : F[X]).Monic := monic_X_pow_sub_C c two_ne_zero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem natDegree_pol : (X ^ 2 - C c : F[X]).natDegree = 2 := natDegree_X_pow_sub_C

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem root_mul_root :
    AdjoinRoot.root (X ^ 2 - C c) * AdjoinRoot.root (X ^ 2 - C c) = AdjoinRoot.of (X ^ 2 - C c) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  linear_combination h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_rep (y : AdjoinRoot (X ^ 2 - C c)) :
    ∃ a b : F, y = AdjoinRoot.of _ a + AdjoinRoot.of _ b * AdjoinRoot.root _ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) f = AdjoinRoot.mk (X ^ 2 - C c) (f %ₘ (X ^ 2 - C c)) := by
    rw [AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div]
    exact ⟨f /ₘ (X ^ 2 - C c), by ring⟩
  have h2 : (f %ₘ (X ^ 2 - C c)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f (monic_pol c) (by
      intro h
      have := natDegree_pol c
      rw [h, natDegree_one] at this
      omega)
    rw [natDegree_pol] at this
    omega
  obtain ⟨b, a, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one h2
  refine ⟨a, b, ?_⟩
  rw [h1, hab, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rep_eq_zero {a b : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ = 0) :
    a = 0 ∧ b = 0 := by
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) (C b * X + C a) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]
    exact h
  by_contra hne
  have h0 : (C b * X + C a : F[X]) ≠ 0 := by
    intro h0
    apply hne
    have ha := congrArg (fun p => coeff p 0) h0
    have hb := congrArg (fun p => coeff p 1) h0
    simp at ha hb
    exact ⟨ha, hb⟩
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_pol c) h0 ?_ h1
  rw [natDegree_pol]
  exact lt_of_le_of_lt natDegree_linear_le one_lt_two

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Supply the required witnesses or components.
-/
theorem rep_inj {a b a' b' : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ =
      AdjoinRoot.of _ a' + AdjoinRoot.of _ b' * AdjoinRoot.root _) : a = a' ∧ b = b' := by
  have := rep_eq_zero c (a := a - a') (b := b - b') (by
    rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

instance finite_adj : Module.Finite F (AdjoinRoot (X ^ 2 - C c)) := (monic_pol c).finite_adjoinRoot

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_adj : finrank F (AdjoinRoot (X ^ 2 - C c)) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_pol c)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_pol]

def conjHom : AdjoinRoot (X ^ 2 - C c) →ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F _) (-AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    have h := root_mul_root c
    show (-AdjoinRoot.root _) ^ 2 - AdjoinRoot.of _ c = 0
    linear_combination h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conjHom_root : conjHom c (AdjoinRoot.root _) = -AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

def conj : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c) :=
  AlgEquiv.ofAlgHom (conjHom c) (conjHom c)
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_root : conj c (AdjoinRoot.root _) = -AdjoinRoot.root _ := conjHom_root c

section

variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the second alternative.
-/
theorem gal_root (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ (AdjoinRoot.root _) = AdjoinRoot.root _ ∨ τ (AdjoinRoot.root _) = -AdjoinRoot.root _ := by
  have h := congrArg τ (root_mul_root c)
  have hc : τ (AdjoinRoot.of _ c) = AdjoinRoot.of _ c := τ.commutes c
  rw [map_mul, hc, ← root_mul_root c] at h
  have h2 : (τ (AdjoinRoot.root _) - AdjoinRoot.root (X ^ 2 - C c)) *
      (τ (AdjoinRoot.root _) + AdjoinRoot.root _) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact Or.inl (sub_eq_zero.1 h3)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h3)

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem gal_cases (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ = 1 ∨ τ = conj c := by
  rcases gal_root c τ with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact AdjoinRoot.algHom_ext (h.trans (conj_root c).symm)

variable [CharZero F]

instance isGalois_adj : IsGalois F (AdjoinRoot (X ^ 2 - C c)) := by
  have : Algebra.IsQuadraticExtension F (AdjoinRoot (X ^ 2 - C c)) := ⟨finrank_adj c⟩
  infer_instance

end

end Formalism.HermitianLattices.Ext.L3.QuadAdj
