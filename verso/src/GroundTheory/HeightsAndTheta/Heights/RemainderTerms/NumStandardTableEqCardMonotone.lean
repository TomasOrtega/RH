import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics

open MvPolynomial Finset

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem card_monotone_equiv_congr {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {n n' : ℕ} (h : n = n') :
    Nat.card {T : α ≃ Fin n // Monotone T} = Nat.card {T : β ≃ Fin n' // Monotone T} := by
  subst h
  exact Nat.card_congr
    { toFun := fun T => ⟨e.symm.toEquiv.trans T.1, fun a b hab => T.2 (e.symm.monotone hab)⟩
      invFun := fun T => ⟨e.toEquiv.trans T.1, fun a b hab => T.2 (e.monotone hab)⟩
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp }

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_youngCells {m : ℕ} (lam : Fin m → ℕ) (x : Fin m × ℕ) :
    x ∈ RestTerms.youngCells lam ↔ x.2 < lam x.1 := by
  unfold RestTerms.youngCells
  simp only [mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨lt_of_lt_of_le h (Finset.single_le_sum (fun i _ => Nat.zero_le (lam i))
      (mem_univ x.1)), h⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_shapeCells {r : ℕ} (la : Fin r → ℕ) (x : ℕ × ℕ) :
    x ∈ IndefiniteRowSideFullHecke.RestTerms.shapeCells la ↔ ∃ h : x.1 < r, x.2 < la ⟨x.1, h⟩ := by
  unfold IndefiniteRowSideFullHecke.RestTerms.shapeCells
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a.2, hb⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x.1, h⟩, x.2, hx, rfl⟩

def cellIso {r : ℕ} (la : Fin r → ℕ) :
    RestTerms.youngCells la ≃o IndefiniteRowSideFullHecke.RestTerms.shapeCells la where
  toFun p := ⟨((p.1.1 : ℕ), p.1.2),
    (mem_shapeCells la _).2 ⟨p.1.1.2, (mem_youngCells la _).1 p.2⟩⟩
  invFun q := ⟨(⟨q.1.1, ((mem_shapeCells la _).1 q.2).1⟩, q.1.2),
    (mem_youngCells la _).2 ((mem_shapeCells la _).1 q.2).2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨c, d⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem numStandardTable_eq_card_monotone {m : ℕ} (lam : Fin m → ℕ) :
    RestTerms.numStandardTable lam =
      Nat.card {T : RestTerms.youngCells lam ≃ Fin (RestTerms.youngCells lam).card //
        Monotone T} := by
  unfold RestTerms.numStandardTable
  refine Nat.card_congr (Equiv.subtypeEquivRight fun T => ?_)
  constructor
  · intro h p q hpq
    have h' := Prod.le_def.1 (Subtype.coe_le_coe.2 hpq)
    exact h p q h'.1 h'.2
  · intro h p q h1 h2
    exact h (Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h1, h2⟩))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem numSYT_eq {r : ℕ} (la : Fin r → ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT la = RestTerms.numStandardTable la := by
  rw [numStandardTable_eq_card_monotone]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  refine (card_monotone_equiv_congr (cellIso la) ?_).symm
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (cellIso la).toEquiv

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem shapeCells_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.shapeCells (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      IndefiniteRowSideFullHecke.RestTerms.shapeCells (RestTerms.hookShape r k b) := by
  ext x
  rw [mem_shapeCells, mem_shapeCells]
  simp only [RestTerms.hookShape, IndefiniteRowSideFullHecke.RestTerms.hookShape]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨by omega, ?_⟩
    split_ifs at hx ⊢ <;> omega
  · rintro ⟨h, hx⟩
    have h' : x.1 < b + 1 := by
      by_contra hc
      split_ifs at hx <;> omega
    refine ⟨h', ?_⟩
    split_ifs at hx ⊢ <;> omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem numSYT_hookShape (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      RestTerms.numStandardTable (RestTerms.hookShape r k b) := by
  rw [← numSYT_eq]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  rw [shapeCells_hookShape r k b hb]

end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
