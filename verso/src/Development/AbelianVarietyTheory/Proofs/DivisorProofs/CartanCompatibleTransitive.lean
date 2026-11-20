import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CartanRefl

open Matrix

variable {n : ℕ}

/- English proof (translation)
Establish `h : ∀ i j, star (M i j) = M j i` using `fun i j => by`. Simplify using `using congrFun (congrFun hM i) j`. Simplify using `only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, h, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.map star = Mᵀ) (x y : Fin n → ℂ) :
    star (x ⬝ᵥ M *ᵥ star y) = y ⬝ᵥ M *ᵥ star x := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by
    simpa using congrFun (congrFun hM i) j
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.CartanRefl
