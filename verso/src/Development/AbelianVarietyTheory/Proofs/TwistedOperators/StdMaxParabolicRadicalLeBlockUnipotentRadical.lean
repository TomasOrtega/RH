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
Rewrite using `[mem_unipRad, mem_parab]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hD⟩ i j hij`. Break down `lt_or_eq_of_le (not_lt.mp hij) with hlt | heq` into its components or cases. Establish `hne : i ≠ j` using `fun hh => (ne_of_lt hlt) (by rw [hh])`.

Rewrite using `[hP i j hlt, Matrix.one_apply_ne hne]`. Take `⟨⟨a, i'⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j'⟩, rfl⟩` from `e.surjective j`. Simplify using `only [blk_apply] at heq`. Substitute `heq` using the available equality.

Rewrite using `[hD]`. Distinguish the cases in `hs : i' = j'`. Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]`.

Introduce `H`. Use `⟨fun i j hji => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Establish `hne : i ≠ j` using `fun hh => (ne_of_lt hji) (by rw [hh])`. Rewrite using `[H i j (not_lt.mpr hji.le), Matrix.one_apply_ne hne]`. Rewrite using `[H _ _ (by simp)]`.

Distinguish the cases in `hs : i = j`. Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]`.
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
Establish `hne : i ≠ j` using `fun hh => (ne_of_lt hij) (by rw [hh])`. Assume the negation of the conclusion as `hc`. Establish `hdet : IsUnit (Matrix.transvection i j (1 : R)).det`. Rewrite using `[Matrix.det_transvection_of_ne _ _ hne]`. Conclude with `isUnit_one`.

Take `⟨t, ht⟩ : ∃ t : GL n R, (t : Matrix n n R) = Matrix.transvection i j (1 : R)` from `⟨Matrix.nonsingInvUnit _ hdet, rfl⟩`. Establish `hent : ∀ k l, (t : Matrix n n R) k l = (1 : Matrix n n R) k l + if i = k ∧ j = l then 1 else 0`. Introduce `k l`. Rewrite using `[ht]`. Simplify using `[Matrix.transvection, Matrix.single_apply]`.

Establish `hmem : t ∈ parab R e`. Rewrite using `[mem_parab]`. Introduce `k l hkl`. Establish `hkl' : k ≠ l` using `fun hh => (ne_of_lt hkl) (by rw [hh])`. Rewrite using `[hent, Matrix.one_apply_ne hkl', zero_add, if_neg]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hc hkl`. Establish `hzero` using `mem_parab.mp (h hmem) i j hij`. Rewrite `hzero` using `[hent, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩]`. Conclude with `one_ne_zero hzero`.
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
Introduce `g hg`. Rewrite `hg`, the goal using `[mem_unipRad_entries]`. Introduce `i j hij`. Conclude with `hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))`.
-/
theorem unipRad_le_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') : unipRad R e' ≤ unipRad R e := by
  intro g hg
  rw [mem_unipRad_entries] at hg ⊢
  intro i j hij
  exact hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))

/- English proof (translation)
Introduce `F _ r a b s h d hd hle`. Conclude with `unipRad_le_of_parab_le hle`.
-/
theorem stdMaxRad_le_unipRad : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  intro F _ r a b s h d hd hle
  exact unipRad_le_of_parab_le hle

end GlobalTheory.RadRev
