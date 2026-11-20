import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coefM_one (z : ℂ) : coefM z 1 = z := by
  simp [coefM, Complex.ext_iff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coefM_neg_one (z : ℂ) : coefM z (-1) = star z := by
  simp [coefM, Complex.ext_iff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coefD_one (z : ℂ) : coefD z 1 = -star z := by
  simp [coefD, Complex.ext_iff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coefD_neg_one (z : ℂ) : coefD z (-1) = -z := by
  simp [coefD, Complex.ext_iff]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem heisOp_eq_sum_mul_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  intro P Q R S c
  unfold heisOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ -
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [raiB, lowB, linePos, lineSign, coefM_one, coefM_neg_one, coefD_one, coefD_neg_one, if_true,
      Bool.false_eq_true, if_false] <;>
    module

end GlobalTheory.CCRFock
