import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScCApplyInlInl

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA2

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def toOm {ι : Type} (X : Matrix ι ι E) (h : ∀ i j, X i j ∈ O) : Matrix ι ι O := Matrix.of fun i j => ⟨X i j, h i j⟩

/- English proof (translation)
Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [scC, liftE, dlast, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;>`. Apply the tactic sequence `split_ifs <;> simp_all [O.one_mem, O.zero_mem]`.
-/
theorem scC_mem (α β : E) (hα : α ∈ O) (hβ : β ∈ O) (i j : Ix r) : scC r α β i j ∈ O := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scC, liftE, dlast, Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp_all [O.one_mem, O.zero_mem]

/- English proof (translation)
Unfold `scC`. Rewrite using `[Matrix.fromBlocks_multiply]`. Establish `hL : liftE (R` using `E) r * dlast r α' = α' • liftE r := by`. Use extensionality with `a b`. Simplify using `only [liftE, dlast, Matrix.mul_diagonal, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs with h1 h2 <;> simp_all`. Establish `hD : dlast r α * dlast r α' = 1`. Rewrite using `[dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `split_ifs <;> simp [h1]`. Simplify using `only [Matrix.smul_mul, hL, hD, h2, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, smul_zero]`. Rewrite using `[← Matrix.fromBlocks_one, ← add_smul]`. Use `congr 1`. Simplify using `[mul_comm]`.
-/
theorem scC_mul_inv (α β α' β' : E) (h1 : α * α' = 1) (h2 : β' = -(β * α')) :
    scC r α β * scC r α' β' = 1 := by
  unfold scC
  rw [Matrix.fromBlocks_multiply]
  have hL : liftE (R := E) r * dlast r α' = α' • liftE r := by
    ext a b
    simp only [liftE, dlast, Matrix.mul_diagonal, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with h1 h2 <;> simp_all
  have hD : dlast r α * dlast r α' = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [h1]
  simp only [Matrix.smul_mul, hL, hD, h2, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, smul_zero]
  rw [← Matrix.fromBlocks_one, ← add_smul]
  congr 1
  simp [mul_comm]

/- English proof (translation)
Rewrite using `[scC, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, dlast, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_eq_single (Fin.last r)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules.
-/
theorem scC_det (α β : E) : (scC r α β).det = α := by
  rw [scC, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, dlast, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (Fin.last r)]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end ScaleA2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
