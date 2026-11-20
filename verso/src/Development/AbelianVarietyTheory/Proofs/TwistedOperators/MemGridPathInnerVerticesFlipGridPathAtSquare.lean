import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

namespace GlobalTheory.SplitFlip

def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

/- English proof (translation)
Apply the tactic sequence `cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring`.
-/
theorem pathInnerDiff_tgt (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring

/- English proof (translation)
Establish `h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·)` using `List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by show pathInnerDiff a.src < pathInnerDiff b.src`. Rewrite using `[← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)`. Conclude with `h.pairwise`.
-/
theorem IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise

/- English proof (translation)
The claim follows from `List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])`.
-/
theorem IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])

/- English proof (translation)
Distinguish the cases in `h1 : e = .theta i j`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : e = .ex i j`. Substitute `h2` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h1, h2]`.
-/
theorem src_flipEdge_pathInner (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]

/- English proof (translation)
Introduce `X hX`. Rewrite `hX` using `[innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map]`. Take `⟨e, he, rfl⟩` from `hX`. Rewrite using `[Function.comp_apply, src_flipEdge_pathInner]`. Establish `hex : Edge.ex i j ∈ γ` using `hp.subset (by simp)`.

Establish `heγ : e ∈ γ` using `List.mem_of_mem_tail he`. Distinguish the cases in `h : e = .ex i j`. Simplify using `only [h, if_true]`. Use `⟨fun H => ?_, fun H => absurd rfl H⟩` and prove the remaining obligations. Simplify using `at H`.

Simplify using `only [h, if_false]`. Use `⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩` and prove the remaining obligations.
-/
theorem mem_innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩

end GlobalTheory.SplitFlip
