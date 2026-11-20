import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOrderedForm

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `nil => exact Interleave.nil`. Consider the case `cons a b ih => exact Interleave.left ih`.
-/
theorem interleave_left_nil (b : List T) : Interleave b [] b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.left ih

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `nil => exact Interleave.nil`. Consider the case `cons a b ih => exact Interleave.right ih`.
-/
theorem interleave_right_nil (b : List T) : Interleave [] b b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.right ih

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact interleave_left_nil b`. Consider the case `left _ ih => exact Interleave.left ih`. Consider the case `right _ ih => exact Interleave.right ih`.
-/
theorem Interleave.append_left {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave (u ++ b) v (w ++ b) := by
  induction h with
  | nil => exact interleave_left_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact interleave_right_nil b`. Consider the case `left _ ih => exact Interleave.left ih`. Consider the case `right _ ih => exact Interleave.right ih`.
-/
theorem Interleave.append_right {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave u (v ++ b) (w ++ b) := by
  induction h with
  | nil => exact interleave_right_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

/- English proof (translation)
Simplify using `[wt]`.
-/
theorem wt_cons (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by
  simp [wt]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Introduce `m n h`. Establish `h0 : m = 0 ∧ n = 0` using `add_eq_zero.1 (by simpa using h.symm)`. Use `⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩` and prove the remaining obligations.

Simplify using `[h0.1]`. Simplify using `[h0.2]`. Consider the case `cons a L ih`. Introduce `m n h`. Establish `ha : a ∈ m + n`.

Rewrite using `[← h]`. Simplify using the standard rewrite rules. Break down `Multiset.mem_add.1 ha with ha | ha` into its components or cases. Establish `hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n`. Apply `(Multiset.cons_inj_right a).1` to reduce the goal to its premises.

Rewrite using `[Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]`. Take `⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩` from `ih (m.erase a) n hL`. Use `⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← Multiset.cons_coe, e₁, Multiset.cons_erase ha]`. Rewrite using `[GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]`.

Conclude with `GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _`. Establish `hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a`. Apply `(Multiset.cons_inj_right a).1` to reduce the goal to its premises. Rewrite using `[Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]`. Take `⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩` from `ih m (n.erase a) hL`.

Use `⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Multiset.cons_coe, e₂, Multiset.cons_erase ha]`. Rewrite using `[GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]`. Conclude with `GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _`.
-/
theorem exists_sublists_interleave (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  classical
  induction L with
  | nil =>
    intro m n h
    have h0 : m = 0 ∧ n = 0 := add_eq_zero.1 (by simpa using h.symm)
    refine ⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩
    · simp [h0.1]
    · simp [h0.2]
  | cons a L ih =>
    intro m n h
    have ha : a ∈ m + n := by
      rw [← h]
      simp
    rcases Multiset.mem_add.1 ha with ha | ha
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih (m.erase a) n hL
      refine ⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩
      · rw [← Multiset.cons_coe, e₁, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih m (n.erase a) hL
      refine ⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩
      · rw [← Multiset.cons_coe, e₂, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _

/- English proof (translation)
Introduce `T s hinj hs m n`. Take `⟨L, hL, hord⟩` from `exists_ordered_form s hinj hs (m + n)`. Take `⟨L₁, L₂, h₁, h₂, c₁, c₂, hi⟩` from `exists_sublists_interleave s L m n hL`. Conclude with `⟨L₁, L₂, L, c₁, c₂, hL, List.Pairwise.sublist h₁ hord, List.Pairwise.sublist h₂ hord, hord, hi⟩`.
-/
theorem exists_common_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m n : Multiset (ASeg T), ∃ L₁ L₂ L : List (ASeg T),
      (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
      (L : Multiset (ASeg T)) = m + n ∧ AOrdered s L₁ ∧ AOrdered s L₂ ∧ AOrdered s L ∧
      Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  intro T s hinj hs m n
  obtain ⟨L, hL, hord⟩ := exists_ordered_form s hinj hs (m + n)
  obtain ⟨L₁, L₂, h₁, h₂, c₁, c₂, hi⟩ := exists_sublists_interleave s L m n hL
  exact ⟨L₁, L₂, L, c₁, c₂, hL, List.Pairwise.sublist h₁ hord, List.Pairwise.sublist h₂ hord,
    hord, hi⟩

end GlobalTheory.CompanionTheory.SegOrder
