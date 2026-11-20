import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Simplify using `only [splitSeq, Set.mem_setOf_eq, List.pairwise_iff_get]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun y hy => ?_, fun i j hij => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.get_of_mem hy`.

Simplify using `using h i i`. Simplify `h i j` using `[hij.ne]`. Simplify `h j i` using `[hij.ne']`. Introduce and unpack `⟨h1, h2⟩ i j`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Rewrite using `[if_neg hij.ne]`. Conclude with `(h2 i j hij).1`. Rewrite using `[if_pos rfl]`. Conclude with `h1 _ (List.get_mem _ _)`. Rewrite using `[if_neg hij.ne']`.

Conclude with `(h2 j i hij).2`.
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
Introduce `l hl l' hs`. Rewrite `hl`, the goal using `[mem_splitSeq_iff_pairwise]`. Conclude with `⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩`.
-/
theorem splitSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (splitSeq R n) := by
  intro l hl l' hs
  rw [mem_splitSeq_iff_pairwise] at hl ⊢
  exact ⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf⟩`. Use `⟨List.ofFn fun i => (w.get i, f i), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Establish `hi : (i : ℕ) < w.length` using `by simpa using i.2`.

Establish `hj : (j : ℕ) < w.length` using `by simpa using j.2`. Use `hf ⟨i, hi⟩ ⟨j, hj⟩` as an intermediate fact. Simplify using `only [List.get_eq_getElem, List.getElem_ofFn] at this ⊢`. Simplify `this` using `[Fin.ext_iff]`. Simplify using `[List.map_ofFn]`.

Conclude with `List.ofFn_get w`. Introduce and unpack `⟨l, hl, rfl⟩`. Use `⟨fun i => (l.get ⟨i, by simpa using i.2⟩).2, fun i j => ?_⟩` and prove the remaining obligations. Use `hl ⟨i, by simpa using i.2⟩ ⟨j, by simpa using j.2⟩` as an intermediate fact. Simplify using `only [List.get_eq_getElem, List.getElem_map] at this ⊢`.

Simplify `this` using `[Fin.ext_iff]`.
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
Introduce `w hw w' hs`. Rewrite `hw`, the goal using `[mem_uniSeq_iff_exists_split]`. Take `⟨l, hl, rfl⟩` from `hw`. Take `⟨l', hl', rfl⟩` from `List.sublist_map_iff.mp hs`. Conclude with `⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩`.
-/
theorem uniSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (uniSeq R n) := by
  intro w hw w' hs
  rw [mem_uniSeq_iff_exists_split] at hw ⊢
  obtain ⟨l, hl, rfl⟩ := hw
  obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
  exact ⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩

end GlobalTheory.SeqCx

/- English proof (translation)
Introduce `R _ n` and use `⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩`.
-/
theorem GlobalTheory.SeqCx.split_uni_closed : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) :=
  fun R _ n => ⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.split_uni_closed`. Consider the case `exact @GlobalTheory.SeqCx.uniSeq_sublist_closed`. Consider the case `exact @GlobalTheory.SeqCx.mem_uniSeq_iff_exists_split`. Consider the case `exact @GlobalTheory.SeqCx.splitSeq_sublist_closed`.

Consider the case `exact @GlobalTheory.SeqCx.mem_splitSeq_iff_pairwise`.
-/
theorem _root_.GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) := by
  first
  | exact @GlobalTheory.SeqCx.split_uni_closed
  | exact @GlobalTheory.SeqCx.uniSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_uniSeq_iff_exists_split
  | exact @GlobalTheory.SeqCx.splitSeq_sublist_closed
  | exact @GlobalTheory.SeqCx.mem_splitSeq_iff_pairwise
end
