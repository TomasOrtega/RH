import Mathlib

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Introduce `R _ _ N r hr A A' B B' X hAB hBA hAB' hBA' hX`. Establish `canc : ∀ P Q : Matrix (Fin N) (Fin N) R, r • P = r • Q → P = Q`. Introduce `P Q h`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Simplify using `only [Matrix.smul_apply, smul_eq_mul] at this`. Conclude with `mul_left_cancel₀ hr this`. Establish `hg : r • (1 + A' * X) = A' * B`. Rewrite using `[smul_add, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB']`. Normalize the expressions using the abelian group laws.

Establish `hh : r • (1 - A * X) = A * B'`. Rewrite using `[smul_sub, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB]`. Normalize the expressions using the abelian group laws. Establish `h1 : (1 + A' * X) * (1 - A * X) = 1`. Apply `canc` to reduce the goal to its premises.

Apply `canc` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul]`. Use `_ = A' * (B * A) * B' := by rw [hg, hh]; simp only [Matrix.mul_assoc]`. Use `_ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by`.

Rewrite using `[hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB']`. Establish `h2 : (1 - A * X) * (1 + A' * X) = 1`. Apply `canc` to reduce the goal to its premises. Apply `canc` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul]`. Use `_ = A * (B' * A') * B := by rw [hg, hh]; simp only [Matrix.mul_assoc]`. Use `_ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by`. Rewrite using `[hBA', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB]`. Use `⟨⟨1 + A' * X, 1 - A * X, h1, h2⟩, ?_⟩` and prove the remaining obligations.

Apply `canc` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `r • ((1 + A' * X) * A) = r • A'`. Rewrite using `[← Matrix.smul_mul, hg, Matrix.mul_assoc, hBA, Matrix.mul_smul, Matrix.mul_one]`.
-/
theorem UpperTheory.V.KT.hnfeq :
    ∀ (R : Type) [CommRing R] [IsDomain R] (N : ℕ) (r : R), r ≠ 0 → ∀ A A' B B' X : Matrix (Fin N) (Fin N) R,
    A * B = r • (1 : Matrix (Fin N) (Fin N) R) → B * A = r • (1 : Matrix (Fin N) (Fin N) R) →
    A' * B' = r • (1 : Matrix (Fin N) (Fin N) R) → B' * A' = r • (1 : Matrix (Fin N) (Fin N) R) →
    B - B' = r • X → ∃ g : GL (Fin N) R, (g : Matrix (Fin N) (Fin N) R) * A = A' := by
  intro R _ _ N r hr A A' B B' X hAB hBA hAB' hBA' hX
  have canc : ∀ P Q : Matrix (Fin N) (Fin N) R, r • P = r • Q → P = Q := by
    intro P Q h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hr this
  have hg : r • (1 + A' * X) = A' * B := by
    rw [smul_add, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB']; abel
  have hh : r • (1 - A * X) = A * B' := by
    rw [smul_sub, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB]; abel
  have h1 : (1 + A' * X) * (1 - A * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 + A' * X) * (1 - A * X)) = (r • (1 + A' * X)) * (r • (1 - A * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A' * (B * A) * B' := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB']
  have h2 : (1 - A * X) * (1 + A' * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 - A * X) * (1 + A' * X)) = (r • (1 - A * X)) * (r • (1 + A' * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A * (B' * A') * B := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB]
  refine ⟨⟨1 + A' * X, 1 - A * X, h1, h2⟩, ?_⟩
  apply canc
  change r • ((1 + A' * X) * A) = r • A'
  rw [← Matrix.smul_mul, hg, Matrix.mul_assoc, hBA, Matrix.mul_smul, Matrix.mul_one]
