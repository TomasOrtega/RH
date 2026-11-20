import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `κ _ n r t _ hr g hg`. Establish `hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n` using `n) r) := by`. Use `Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_` and prove the remaining obligations. Establish `hji : j.val < r ∧ ¬ i.val < r`. Unfold `Formalism.L2.DIV.blk2 at hij`.

Apply the tactic sequence `by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢`. Use `hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]`. Conclude with `Nat.succ_pos _`. Rewrite using `[Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hg, fun i j hi hj => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩`. Simplify using `only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1`.

Rewrite using `[Matrix.one_apply]`. Simplify using `only [Fin.ext_iff]`. Conclude with `h1`. Introduce and unpack `⟨-, h⟩`. Use extensionality with `i j`.

Rewrite using `[Matrix.submatrix_apply, h _ _ i.2 j.2]`. Simplify using `[Matrix.one_apply]`.
-/
theorem topBlock_eq_one_iff_mem_colHK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  intro κ _ n r t _ hr g hg
  have hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n := n) r) := by
    refine Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_
    have hji : j.val < r ∧ ¬ i.val < r := by
      unfold Formalism.L2.DIV.blk2 at hij
      by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢
    refine hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)
    rw [Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]
    exact Nat.succ_pos _
  rw [Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]
  constructor
  · intro h
    refine ⟨hg, fun i j hi hj => ?_⟩
    have h1 := congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1
    rw [Matrix.one_apply]
    simp only [Fin.ext_iff]
    exact h1
  · rintro ⟨-, h⟩
    ext i j
    rw [Matrix.submatrix_apply, h _ _ i.2 j.2]
    simp [Matrix.one_apply]

end GlobalTheory
