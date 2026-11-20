import Mathlib

namespace GlobalTheory.LowerTriangularMul

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i k with hik | hki` into its components or cases. Rewrite using `[hA i k hik, zero_mul]`.

Rewrite using `[hB k j (lt_of_le_of_lt hki hij), mul_zero]`.
-/
theorem lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with hik | hki
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hki hij), mul_zero]

/- English proof (translation)
Introduce `A B hA hB` and use `lowerTriangular_mul A B hA hB`.
-/
theorem main : ∀ {S : Type} [inst : CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S), (∀ (i j : Fin n), i < j → A i j = (0 : S)) → (∀ (i j : Fin n), i < j → B i j = (0 : S)) → ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) :=
  fun A B hA hB => lowerTriangular_mul A B hA hB

end GlobalTheory.LowerTriangularMul
