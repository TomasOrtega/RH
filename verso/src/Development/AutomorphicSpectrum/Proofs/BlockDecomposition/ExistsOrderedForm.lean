import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

/- English proof (translation)
Establish `irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start`. Introduce and unpack `a ⟨j, hj, h⟩`. Conclude with `hs a.start j hj h.symm`. Proceed by induction on `m using Multiset.induction_on with`. Consider the case `empty => exact absurd rfl hm`.

Consider the case `cons x m ih`. Distinguish the cases in `hm' : m = 0`. Substitute `hm'` using the available equality. Use `⟨x, Multiset.mem_cons_self x 0, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Establish `hbx : b = x` using `by simpa using hb`. Substitute `hbx` using the available equality. Conclude with `irr b`. Take `⟨a, ham, hmax⟩` from `ih hm'`. Distinguish the cases in `hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start`.

Take `⟨j, hj, hxa⟩` from `hax`. Use `⟨x, Multiset.mem_cons_self x m, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Break down `Multiset.mem_cons.mp hb with rfl | hbm` into its components or cases. Conclude with `irr b`.

Introduce and unpack `⟨i, hi, hbx⟩`. Use `hmax b hbm ⟨i + j, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hbx, hxa, Function.iterate_add_apply]`. Use `⟨a, Multiset.mem_cons_of_mem ham, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Break down `Multiset.mem_cons.mp hb with rfl | hbm` into its components or cases. Conclude with `hax`. Conclude with `hmax b hbm`.
-/
theorem exists_last_start (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by
  have irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start := by
    rintro a ⟨j, hj, h⟩
    exact hs a.start j hj h.symm
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons x m ih =>
    by_cases hm' : m = 0
    · subst hm'
      refine ⟨x, Multiset.mem_cons_self x 0, ?_⟩
      intro b hb
      have hbx : b = x := by simpa using hb
      subst hbx
      exact irr b
    · obtain ⟨a, ham, hmax⟩ := ih hm'
      by_cases hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start
      · obtain ⟨j, hj, hxa⟩ := hax
        refine ⟨x, Multiset.mem_cons_self x m, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact irr b
        · rintro ⟨i, hi, hbx⟩
          refine hmax b hbm ⟨i + j, by omega, ?_⟩
          rw [hbx, hxa, Function.iterate_add_apply]
      · refine ⟨a, Multiset.mem_cons_of_mem ham, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact hax
        · exact hmax b hbm

/- English proof (translation)
Introduce `T s _ hs m`. Proceed by induction on `hn : Multiset.card m generalizing m with`. Consider the case `zero`. Use `⟨[], ?_, List.Pairwise.nil⟩` and prove the remaining obligations. Simplify using `using (Multiset.card_eq_zero.mp hn).symm`.

Consider the case `succ n ih`. Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hn`. Take `⟨a, ham, hmax⟩` from `exists_last_start s hs m hm`.

Establish `hcard : Multiset.card (m.erase a) = n`. Rewrite using `[Multiset.card_erase_of_mem ham, hn]`. Both sides reduce to the same expression. Take `⟨L, hL, hord⟩` from `ih (m.erase a) hcard`. Use `⟨a :: L, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Multiset.cons_coe, hL]`. Conclude with `Multiset.cons_erase ham`. Use `List.pairwise_cons.mpr ⟨?_, hord⟩` and prove the remaining obligations. Introduce `b hb hprec`. Establish `hbm : b ∈ m`.

Establish `: b ∈ (L : Multiset (ASeg T))` using `by simpa using hb`. Rewrite `this` using `[hL]`. Conclude with `Multiset.mem_of_mem_erase this`. Conclude with `hmax b hbm hprec.2`.
-/
theorem exists_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by
  classical
  intro T s _ hs m
  induction hn : Multiset.card m generalizing m with
  | zero =>
    refine ⟨[], ?_, List.Pairwise.nil⟩
    simpa using (Multiset.card_eq_zero.mp hn).symm
  | succ n ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    obtain ⟨a, ham, hmax⟩ := exists_last_start s hs m hm
    have hcard : Multiset.card (m.erase a) = n := by
      rw [Multiset.card_erase_of_mem ham, hn]
      rfl
    obtain ⟨L, hL, hord⟩ := ih (m.erase a) hcard
    refine ⟨a :: L, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hL]
      exact Multiset.cons_erase ham
    · refine List.pairwise_cons.mpr ⟨?_, hord⟩
      intro b hb hprec
      have hbm : b ∈ m := by
        have : b ∈ (L : Multiset (ASeg T)) := by simpa using hb
        rw [hL] at this
        exact Multiset.mem_of_mem_erase this
      exact hmax b hbm hprec.2

end GlobalTheory.CompanionTheory.SegOrder
