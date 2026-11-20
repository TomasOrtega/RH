import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplTwoRow

def twoBlock (n : ℕ) (a b r s : ℤ) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℤ :=
  Matrix.of (vecCons (vecCons a (vecCons b 0))
    (vecCons (vecCons (-s) (vecCons r 0)) fun k => vecCons 0 (vecCons 0 (Pi.single k 1))))

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>`. Apply the tactic sequence `simp [twoBlock, Fin.sum_univ_succ, Matrix.one_apply, Pi.single_apply] <;>`.

Apply the tactic sequence `first | linarith | (split_ifs <;> simp_all [Fin.ext_iff]) | simp [Fin.ext_iff]`.
-/
theorem twoBlock_mul_transpose {n : ℕ} {c d x y : ℤ} (h : x * c + y * d = 1) :
    twoBlock n c d x y * (twoBlock n x y c d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
  simp [twoBlock, Fin.sum_univ_succ, Matrix.one_apply, Pi.single_apply] <;>
  first | linarith | (split_ifs <;> simp_all [Fin.ext_iff]) | simp [Fin.ext_iff]

end PSymplTwoRow

open PSymplTwoRow in

/- English proof (translation)
Introduce `n c d x y h`. Use `⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SymplecticGroup.mem_iff]`. Establish `h1` using `twoBlock_mul_transpose (n := n) h`. Establish `h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1`.

Rewrite using `[← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]`. Simplify using `[J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]`. Use function extensionality and compare the values at `z`. Break down `z with i | i` into its components or cases. Apply the tactic sequence `refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`.

Simplify using `[symplCons, twoBlock]`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`. Simplify using `[symplCons]`.
-/
theorem SymplTwoRow.proof : SymplTwoRow.Statement := by
  intro n c d x y h
  refine ⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff]
    have h1 := twoBlock_mul_transpose (n := n) h
    have h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1 := by
      rw [← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]
  · funext z
    rcases z with i | i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons, twoBlock]
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons]

end GroundTheory.Heights₂.Heights
