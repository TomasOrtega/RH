import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart

noncomputable section

open NumberField

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E]

def expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp X).unit

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    (expGLi a X).val = NormedSpace.exp X := rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul] exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))`.
-/
theorem expGLi_add_smul (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expGLi a ((s + t) • X) = expGLi a (s • X) * expGLi a (t • X) :=
  Units.ext (by
    rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))

/- English proof (translation)
The claim follows from `Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])`.
-/
@[simp] theorem expGLi_zero (a : ℕ) : expGLi a (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
  Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])

end GlobalTheory.CuspRep
