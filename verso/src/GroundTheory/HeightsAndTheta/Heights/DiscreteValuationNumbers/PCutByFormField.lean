import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace CutByFormField

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc, Matrix.cons_val_succ]`.
-/
theorem vecCons_comp_finRotate {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

end CutByFormField

end

end GroundTheory.Heights₂.Heights.NumbersDVR
