import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt

/- English proof (translation)
Introduce `E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx`. Take `⟨w, rfl⟩` from `ha`. Take `⟨j, hj, rfl⟩` from `List.getElem_of_mem hx`. Establish `h1` using `w.2.1.1 v j hj`. Establish `hnode` using `(hG v).2.2.2.2.2`.

Establish `hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v)`. Introduce `Y hY`. Simplify using `only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY`. Simplify using `only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]`. Apply the tactic sequence `constructor <;> linarith [hY.1, hY.2]`.

Distinguish the cases in `hp : ((w.1 v)[j]'hj).1`. Rewrite `h1` using `[if_pos hp]`. Establish `hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v`. Break down `Finset.mem_union.1 h1 with h | h` into its components or cases. Conclude with `Or.inl ⟨_, h⟩`.

Conclude with `Or.inr h`. Conclude with `hcut _ (hnode _ hy).1`. Rewrite `h1` using `[if_neg hp]`. Establish `hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v`. Break down `Finset.mem_union.1 h1 with h | h` into its components or cases.

Conclude with `Or.inl ⟨_, h⟩`. Conclude with `Or.inr h`. Use `hcut _ (hnode _ hy).2.1` as an intermediate fact. Simplify using `using this`.
-/
theorem admissible_in_truncation_holds : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this

end Formalism.FourierDecayAlt.P.CutMP
