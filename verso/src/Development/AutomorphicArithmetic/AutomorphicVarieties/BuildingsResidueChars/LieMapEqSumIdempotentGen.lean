import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `R _ _ ι _ n A _ _ _ _ D l X`. Establish `key : ∀ i j, ∑ τ, D.ch τ (X i j) • gen D l τ i j = l (Matrix.single i j (X i j))`. Introduce `i j`. Simplify using `only [gen, ← map_smul, ← map_sum, ← D.mul_e, ← Finset.mul_sum, D.sum, mul_one, unitMap_tmul, one_smul]`. Use `conv_rhs =>`.

Rewrite using `[Finset.sum_comm]`. Use `arg 2`. Use extensionality with `i`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [key, ← map_sum]`.

Use `congr 1`. Conclude with `Matrix.matrix_eq_sum_single X`.
-/
theorem UpperTheory.lieMap_eq_sum_idempotent_gen :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (X : Matrix (Fin n) (Fin n) R), l X = ∑ τ, ∑ i, ∑ j, D.ch τ (X i j) • gen D l τ i j := by
  intro R _ _ ι _ n A _ _ _ _ D l X
  have key : ∀ i j, ∑ τ, D.ch τ (X i j) • gen D l τ i j = l (Matrix.single i j (X i j)) := by
    intro i j
    simp only [gen, ← map_smul, ← map_sum, ← D.mul_e, ← Finset.mul_sum, D.sum, mul_one,
      unitMap_tmul, one_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  simp only [key, ← map_sum]
  congr 1
  exact Matrix.matrix_eq_sum_single X
