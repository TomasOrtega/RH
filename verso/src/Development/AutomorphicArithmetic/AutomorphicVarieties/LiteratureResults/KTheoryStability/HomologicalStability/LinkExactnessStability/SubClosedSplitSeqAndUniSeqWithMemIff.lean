import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_splitSeq_iff_pairwise (R : Type) [CommRing R] (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))) :
    l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧
      l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0 := by
  simp only [splitSeq, Set.mem_setOf_eq, List.pairwise_iff_get]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hy
      simpa using h i i
    · simpa [hij.ne] using h i j
    · simpa [hij.ne'] using h j i
  · rintro ⟨h1, h2⟩ i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg hij.ne]
      exact (h2 i j hij).1
    · rw [if_pos rfl]
      exact h1 _ (List.get_mem _ _)
    · rw [if_neg hij.ne']
      exact (h2 j i hij).2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem splitSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (splitSeq R n) := by
  intro l hl l' hs
  rw [mem_splitSeq_iff_pairwise] at hl ⊢
  exact ⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem mem_uniSeq_iff_exists_split (R : Type) [CommRing R] (n : ℕ) (w : List (Fin n → R)) :
    w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨List.ofFn fun i => (w.get i, f i), ?_, ?_⟩
    · intro i j
      have hi : (i : ℕ) < w.length := by simpa using i.2
      have hj : (j : ℕ) < w.length := by simpa using j.2
      have := hf ⟨i, hi⟩ ⟨j, hj⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn] at this ⊢
      simpa [Fin.ext_iff] using this
    · simp [List.map_ofFn]
      exact List.ofFn_get w
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => (l.get ⟨i, by simpa using i.2⟩).2, fun i j => ?_⟩
    have := hl ⟨i, by simpa using i.2⟩ ⟨j, by simpa using j.2⟩
    simp only [List.get_eq_getElem, List.getElem_map] at this ⊢
    simpa [Fin.ext_iff] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem uniSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (uniSeq R n) := by
  intro w hw w' hs
  rw [mem_uniSeq_iff_exists_split] at hw ⊢
  obtain ⟨l, hl, rfl⟩ := hw
  obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
  exact ⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩

end GlobalTheory.SeqCx

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem GlobalTheory.SeqCx.split_uni_closed : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) :=
  fun R _ n => ⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) := by
  first
  | exact @GlobalTheory.SeqCx.split_uni_closed
  | exact @GlobalTheory.SeqCx.uniSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_uniSeq_iff_exists_split
  | exact @GlobalTheory.SeqCx.splitSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_splitSeq_iff_pairwise
end
