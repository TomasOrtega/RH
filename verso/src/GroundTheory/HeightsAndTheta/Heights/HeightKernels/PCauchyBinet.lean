import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Equiv

namespace CauchyBinetAlt

variable {R : Type*} [CommRing R] {j N : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_eq_sum (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem det_submatrix_eq_zero (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall, exists_prop] at hp
  obtain ⟨a, b, hab, hne⟩ := hp
  exact det_zero_of_column_eq hne fun k => by simp [hab]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem minor_mul (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by
  rw [det_apply' (rowsOf B I), mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w) = (colsOf A I).submatrix id w := by
    ext a b
    rfl
  rw [h, det_permute']
  simp only [rowsOf, submatrix_apply, id]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sum_reindex {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hg p hp))]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨I, w⟩ _
    simp only [mem_filter, mem_univ, true_and]
    exact (I.1.orderEmbOfFin I.2).injective.comp w.injective
  · rintro ⟨I, w⟩ _ ⟨J, w'⟩ _ h
    simp only at h
    have key : ∀ (K : {I : Finset (Fin N) // I.card = j}) (v : Perm (Fin j)) (x : Fin N),
        x ∈ K.1 ↔ ∃ a, (K.1.orderEmbOfFin K.2 ∘ v) a = x := by
      intro K v x
      rw [← Finset.mem_coe, ← range_orderEmbOfFin K.1 K.2, Set.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨v.symm a, by simpa using ha⟩, fun ⟨a, ha⟩ => ⟨v a, ha⟩⟩
    have hIJ : I = J := by
      apply Subtype.ext
      ext x
      rw [key I w x, key J w' x, h]
    subst hIJ
    have hw : w = w' := Equiv.ext fun a => (I.1.orderEmbOfFin I.2).injective (congrFun h a)
    rw [hw]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hI : (univ.image p).card = j := by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
    let w0 : Fin j → Fin j := fun a =>
      ((univ.image p).orderIsoOfFin hI).symm ⟨p a, mem_image_of_mem p (mem_univ a)⟩
    have hw0 : Function.Injective w0 := by
      intro a b hab
      exact hp (congrArg Subtype.val (((univ.image p).orderIsoOfFin hI).symm.injective hab))
    refine ⟨(⟨univ.image p, hI⟩, Equiv.ofBijective w0 (Finite.injective_iff_bijective.mp hw0)),
      mem_univ _, ?_⟩
    funext a
    show ((univ.image p).orderEmbOfFin hI) (w0 a) = p a
    rw [← coe_orderIsoOfFin_apply]
    simp only [w0, OrderIso.apply_symm_apply]
  · intro x _
    rfl

end CauchyBinetAlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem CauchyBinet.proof : CauchyBinet.Statement := by
  intro R _ j N A B
  rw [CauchyBinetAlt.det_mul_eq_sum, CauchyBinetAlt.sum_reindex _ (fun p hp => by
    rw [CauchyBinetAlt.det_submatrix_eq_zero A hp, mul_zero])]
  exact Finset.sum_congr rfl fun I _ => (CauchyBinetAlt.minor_mul A B I).symm

end GroundTheory.Heights₂.Heights
