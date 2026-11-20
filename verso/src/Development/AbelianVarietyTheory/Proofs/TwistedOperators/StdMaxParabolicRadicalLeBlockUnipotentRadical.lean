import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.RadRev

open Matrix

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem mem_unipRad_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.mp hij) with hlt | heq
    · have hne : i ≠ j := fun hh => (ne_of_lt hlt) (by rw [hh])
      rw [hP i j hlt, Matrix.one_apply_ne hne]
    · obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at heq
      subst heq
      rw [hD]
      by_cases hs : i' = j'
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]
  · intro H
    refine ⟨fun i j hji => ?_, fun a i j => ?_⟩
    · have hne : i ≠ j := fun hh => (ne_of_lt hji) (by rw [hh])
      rw [H i j (not_lt.mpr hji.le), Matrix.one_apply_ne hne]
    · rw [H _ _ (by simp)]
      by_cases hs : i = j
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [∀ a, Fintype (m' a)]
  [∀ a, DecidableEq (m' a)] in

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem blk_lt_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') {i j : n} (hij : blk e' j < blk e' i) : blk e j < blk e i := by
  have hne : i ≠ j := fun hh => (ne_of_lt hij) (by rw [hh])
  by_contra hc
  have hdet : IsUnit (Matrix.transvection i j (1 : R)).det := by
    rw [Matrix.det_transvection_of_ne _ _ hne]
    exact isUnit_one
  obtain ⟨t, ht⟩ : ∃ t : GL n R, (t : Matrix n n R) = Matrix.transvection i j (1 : R) :=
    ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩
  have hent : ∀ k l, (t : Matrix n n R) k l = (1 : Matrix n n R) k l + if i = k ∧ j = l then 1 else 0 := by
    intro k l
    rw [ht]
    simp [Matrix.transvection, Matrix.single_apply]
  have hmem : t ∈ parab R e := by
    rw [mem_parab]
    intro k l hkl
    have hkl' : k ≠ l := fun hh => (ne_of_lt hkl) (by rw [hh])
    rw [hent, Matrix.one_apply_ne hkl', zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hc hkl
  have hzero := mem_parab.mp (h hmem) i j hij
  rw [hent, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩] at hzero
  exact one_ne_zero hzero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem unipRad_le_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') : unipRad R e' ≤ unipRad R e := by
  intro g hg
  rw [mem_unipRad_entries] at hg ⊢
  intro i j hij
  exact hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem stdMaxRad_le_unipRad : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  intro F _ r a b s h d hd hle
  exact unipRad_le_of_parab_le hle

end GlobalTheory.RadRev
