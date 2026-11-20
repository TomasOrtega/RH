import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock

namespace GlobalTheory.UnipRadThree

/- English proof (translation)
Take `⟨⟨a, x⟩, rfl⟩` from `(place3 h2).surjective i`. Rewrite using `[blk_apply]`. Establish `hv` using `stdBlocks_val (sz3 d) (three_block_size_sum h2) a x`. Establish `hx` using `x.2`. Simplify using `only [GlobalTheory.JacBlock₂.blk]`.

Express the relevant statement in the definitionally equal form `(((stdBlocks (sz3 d) (three_block_size_sum h2)) ⟨a, x⟩ : Fin d) : ℕ) = _ at hv`. Unfold `place3`. Rewrite using `[hv]`. Apply the tactic sequence `fin_cases a <;> simp [sz3, Fin.sum_univ_succ] at hx ⊢ <;> (try split_ifs) <;> omega`.
-/
theorem blk_place3_val {d : ℕ} (h2 : 2 ≤ d) (i : Fin d) :
    ((blk (place3 h2) i : Fin 3) : ℕ) = GlobalTheory.JacBlock₂.blk i := by
  obtain ⟨⟨a, x⟩, rfl⟩ := (place3 h2).surjective i
  rw [blk_apply]
  have hv := stdBlocks_val (sz3 d) (three_block_size_sum h2) a x
  have hx := x.2
  simp only [GlobalTheory.JacBlock₂.blk]
  change (((stdBlocks (sz3 d) (three_block_size_sum h2)) ⟨a, x⟩ : Fin d) : ℕ) = _ at hv
  unfold place3
  rw [hv]
  fin_cases a <;> simp [sz3, Fin.sum_univ_succ] at hx ⊢ <;> (try split_ifs) <;> omega

/- English proof (translation)
Introduce `k _ d h2 u hu`. Take `⟨hp, hd⟩` from `mem_unipRad.1 hu`. Establish `hb` using `blk_place3_val h2`. Use `⟨fun i => ?_, fun i j hij hnlt => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, x⟩, rfl⟩` from `(place3 h2).surjective i`.

Simplify using `using hd a x x`. Break down `lt_trichotomy (GlobalTheory.JacBlock₂.blk j) (GlobalTheory.JacBlock₂.blk i) with h | h | h` into its components or cases. Use `mem_parab.1 hp i j ?_` and prove the remaining obligations. Rewrite using `[Fin.lt_iff_val_lt_val, hb, hb]`. Conclude with `h`.

Establish `he : blk (place3 h2) i = blk (place3 h2) j` using `Fin.ext (by rw [hb, hb, h])`. Take `⟨⟨a, x⟩, rfl⟩` from `(place3 h2).surjective i`. Take `⟨⟨b, y⟩, rfl⟩` from `(place3 h2).surjective j`. Simplify using `only [blk_apply] at he`. Substitute `he` using the available equality.

Establish `hxy : x ≠ y` using `fun hxy => hij (by rw [hxy])`. Rewrite using `[hd a x y, Matrix.one_apply_ne hxy]`. Conclude with `absurd h hnlt`.
-/
theorem isUnipStd_of_mem_unipRad : ∀ (k : Type) [Field k] (d : ℕ) (h2 : 2 ≤ d) (u : GL (Fin d) k),
    u ∈ unipRad k (place3 h2) → GlobalTheory.JacBlock₂.IsUnipStd u := by
  intro k _ d h2 u hu
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hu
  have hb := blk_place3_val h2
  refine ⟨fun i => ?_, fun i j hij hnlt => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := (place3 h2).surjective i
    simpa using hd a x x
  · rcases lt_trichotomy (GlobalTheory.JacBlock₂.blk j) (GlobalTheory.JacBlock₂.blk i) with h | h | h
    · refine mem_parab.1 hp i j ?_
      rw [Fin.lt_iff_val_lt_val, hb, hb]; exact h
    · have he : blk (place3 h2) i = blk (place3 h2) j := Fin.ext (by rw [hb, hb, h])
      obtain ⟨⟨a, x⟩, rfl⟩ := (place3 h2).surjective i
      obtain ⟨⟨b, y⟩, rfl⟩ := (place3 h2).surjective j
      simp only [blk_apply] at he
      subst he
      have hxy : x ≠ y := fun hxy => hij (by rw [hxy])
      rw [hd a x y, Matrix.one_apply_ne hxy]
    · exact absurd h hnlt

end GlobalTheory.UnipRadThree
