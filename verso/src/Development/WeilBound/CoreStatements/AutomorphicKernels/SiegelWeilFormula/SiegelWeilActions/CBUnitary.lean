import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DMEqDiag
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} (i₀ : Fin n) (em : Fin k → Fin n)

def cB (u v : Fin k → R) (z : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (1 + ∑ j, Matrix.single i₀ (em j) (u j)) (Matrix.single i₀ i₀ z) 0 (1 - ∑ j, Matrix.single (em j) i₀ (v j))

variable {i₀ em}

/- English proof (translation)
Establish `hPP : ∀ w w' : Fin k → R, (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0`. Introduce `w w'`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _`. Establish `hQQ : ∀ w w' : Fin k → R, (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0`. Introduce `w w'`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _`. Establish `hPZ : ∀ (w : Fin k → R) (c : R), (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0`. Introduce `w c`. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _`. Establish `hZQ : ∀ (w : Fin k → R) (c : R), Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0`. Introduce `w c`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _`.

Simplify using `only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg, Finset.sum_neg_distrib]`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Apply the tactic sequence `simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul, hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>`. Normalize the expressions using the abelian group laws.
-/
theorem cB_mul (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z : R) : cB i₀ em u v z * cB i₀ em (-u) (-v) (-z) = 1 := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg,
    Finset.sum_neg_distrib]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul,
      hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>
    abel

/- English proof (translation)
Establish `hPP : ∀ w w' : Fin k → R, (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0`. Introduce `w w'`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _`. Establish `hQQ : ∀ w w' : Fin k → R, (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0`. Introduce `w w'`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _`. Establish `hPZ : ∀ (w : Fin k → R) (c : R), (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0`. Introduce `w c`. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _`. Establish `hZQ : ∀ (w : Fin k → R) (c : R), Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0`. Introduce `w c`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _`.

Establish `hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M` using `fun M => (RingHom.mapMatrix_apply f M).symm`. Simplify using `only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpos …`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]`. Rewrite using `[Matrix.fromBlocks_inj]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [mul_zero, zero_mul, add_zero]`. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]`. Normalize the expressions using the abelian group laws. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]`. Use `congr 1`.

Simplify using `only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]`. Normalize the expressions using the abelian group laws. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one, mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]`. Rewrite using `[← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]`.
-/
theorem cB_unitary (hem : ∀ j, em j ≠ i₀) (f : R →+* R) (hf : ∀ a, f (f a) = a) (e : R) (he : e * e = 1)
    (u : Fin k → R) (z : R) (hz : f z = -(e * z)) :
    (cB i₀ em u (fun j => f (u j)) z)ᵀ * kunf.jw n e * (cB i₀ em u (fun j => f (u j)) z).map f = kunf.jw n e := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M := fun M =>
    (RingHom.mapMatrix_apply f M).symm
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_sum, Matrix.transpose_single, hmap,
    map_add, map_sub, map_one, map_zero, map_sum]
  simp only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_zero, zero_mul, add_zero]
  · simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    congr 1
    simp only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]
    rw [← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
