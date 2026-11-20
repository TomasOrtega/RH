import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem blkOf_eq_coarse {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blkOf r t : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blkOf, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blkOf, h, Formalism.L2.Col.blkIdx, h2, Nat.div_eq_of_lt h2]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem twoBlocks_eq_coarse_of_add {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blk2 r : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blk2, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blk2, h, Formalism.L2.Col.blkIdx, h2]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem lowerBlockDet_coarse_partition_eq_blockDet_upperTri {κ : Type} [CommRing κ] {n r t : ℕ} (g : GL (Fin n) κ)
    (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]) :
    Formalism.L2.DIV.dBlk (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) 1 g =
      Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  have hg' : g ∈ Formalism.L2.DIV.blockTri (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) := hg
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hg', Formalism.L2.Col.blkDet_val]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem secondBlockDet_eq_blockDet_of_sum_partitions : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  intro κ _ n r t hn g hg
  refine ⟨?_, ?_⟩
  · rw [blkOf_eq_coarse hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg
  · rw [twoBlocks_eq_coarse_of_add hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg

end GlobalTheory
