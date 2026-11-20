import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Establish `ha` using `a.isLt`. Distinguish the cases in `h : a.val < r`. Rewrite using `[Formalism.L2.Col.coarse_of_lt h]`. Simplify using `[Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]`. Establish `h' : r ≤ a.val` using `Nat.not_lt.mp h`.

Rewrite using `[Formalism.L2.Col.coarse_of_le h']`. Establish `hlt : a.val - r < t` using `by omega`. Establish `hd : (a.val - r) / t = 0` using `Nat.div_eq_of_lt hlt`. Simplify using `[Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]`.
-/
theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

/- English proof (translation)
Introduce `κ _ n r t hn g`. Rewrite using `[Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]`. Simplify using `only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]`.
-/
theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
