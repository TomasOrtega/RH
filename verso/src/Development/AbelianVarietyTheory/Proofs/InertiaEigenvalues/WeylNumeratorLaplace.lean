import Mathlib
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `a b α β l`. Rewrite using `[Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]`. Use `Finset.sum_congr rfl (fun J _ => ?_)` and prove the remaining obligations. Rewrite using `[Nat.add_comm (a * (a - 1) / 2)]`. Use `congr 2`.

Use `congr 1`. Use extensionality with `i k`. Simplify using `[Matrix.submatrix]`. Use `congr 1`. Use extensionality with `i k`.

Simplify using `[Matrix.submatrix]`.
-/
theorem weylNumerator_laplace : ∀ (a b : ℕ) (α : Fin a → ℂˣ) (β : Fin b → ℂˣ) (l : Fin (a + b) → ℤ), (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α β i : ℂˣ) ^ l j : ℂˣ) : ℂ)).det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * (Matrix.of fun i k : Fin a => ((α i ^ l (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det * (Matrix.of fun i k : Fin b => ((β i ^ l (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det := by
  intro a b α β l
  rw [Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [Nat.add_comm (a * (a - 1) / 2)]
  congr 2
  · congr 1
    ext i k
    simp [Matrix.submatrix]
  · congr 1
    ext i k
    simp [Matrix.submatrix]

end GlobalTheory
