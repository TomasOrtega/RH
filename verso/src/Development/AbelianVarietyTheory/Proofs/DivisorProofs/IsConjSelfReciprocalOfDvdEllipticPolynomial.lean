import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SelfRecipFactor

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isSelfRecip_of_dvd_ell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]),
    P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P →
      GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  intro E _ _ _ n P hP Q hQm hQi hQP
  obtain ⟨hPm, -, -, hroots⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hnorm : ∀ z : ℂ, (Q.map τ).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    apply hroots τ z
    rw [mem_roots (Polynomial.map_ne_zero hP0)]
    obtain ⟨R, rfl⟩ := hQP
    have hz' : eval z (Q.map τ) = 0 := hz
    simp [IsRoot, Polynomial.map_mul, eval_mul, hz']
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    have h : (Q.map τ).IsRoot 0 := by
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hnorm 0 h
    simp at this
  set d := Q.natDegree with hd
  set c : E →+* E := (IsCMField.complexConj E : E →+* E) with hc
  have hτc : τ.comp c = (starRingEnd ℂ).comp τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hcQ0 : c (Q.coeff 0) ≠ 0 := by
    simpa using hQ0
  set S := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.sharp E d Q with hS
  have hSdef : S = C (c (Q.coeff 0))⁻¹ * reflect d (Q.map c) := rfl
  have hdegc : (Q.map c).natDegree = d := natDegree_map c
  have hSm : S.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one d
    · rw [hSdef]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_reflect_le.trans ?_
      rw [hdegc, max_self]
    · rw [hSdef, coeff_C_mul, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map]
      exact inv_mul_cancel₀ hcQ0
  have hSdeg : S.natDegree ≤ d := by
    rw [hSdef]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_reflect_le.trans ?_
    rw [hdegc, max_self]

  have hdeg : 0 < (Q.map τ).degree := by
    rw [degree_map]; exact degree_pos_of_irreducible hQi
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : ‖z‖ = 1 := hnorm z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz1; simp at hz1
  have hzinv : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hz1
  have hQz : eval₂ τ z Q = 0 := by
    have : eval z (Q.map τ) = 0 := hz
    rwa [eval_map] at this
  have hSz : eval₂ τ z S = 0 := by
    letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have key := eval₂_reflect_mul_pow τ (z⁻¹) d (Q.map c) hdegc.le
    rw [invOf_eq_inv, inv_inv, eval₂_map, hτc, hzinv, ← Polynomial.hom_eval₂, hQz, map_zero] at key
    have hr : eval₂ τ z (reflect d (Q.map c)) = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ ((_root_.map_ne_zero _).2 hz0))
    rw [hSdef, eval₂_mul, hr, mul_zero]
  have hdvd : Q ∣ S := by
    by_contra h
    obtain ⟨a, b, hab⟩ := (hQi.coprime_iff_not_dvd).2 h
    have := congrArg (eval₂ τ z) hab
    rw [eval₂_add, eval₂_mul, eval₂_mul, hQz, hSz, eval₂_one] at this
    simp at this
  refine ⟨hQm, hQi, rfl, hQ0, ?_⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le hQm hSm hdvd hSdeg).symm

end GlobalTheory.SelfRecipFactor
