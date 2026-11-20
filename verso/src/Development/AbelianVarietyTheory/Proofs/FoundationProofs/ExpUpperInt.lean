import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Establish `hdet : (0 : ℤ) < (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det`. Simplify using `[Matrix.det_fin_two]`. Check the signs of the components of the expression. Establish `e : ∀ i j, ent (toGQ !![a, b; 0, d]) i j = ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)`. Introduce `i j`.

Rewrite using `[ent, toGQ, dif_pos hdet]`. Both sides reduce to the same expression. Establish `h` using `X.exp_upper (toGQ !![a, b; 0, d]) (by rw [e]; simp) f r`. Simplify `h` using `[e]`.
-/
theorem Tower.exp_upper_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (a b d : ℤ)
    (ha : 0 < a) (hd : 0 < d) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![a, b; 0, d]) f)).coeff (r * a / d) = eOm ε (r * b / d) * (X.exp f).coeff r := by
  have hdet : (0 : ℤ) < (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; positivity
  have e : ∀ i j, ent (toGQ !![a, b; 0, d]) i j = ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j; rw [ent, toGQ, dif_pos hdet]; rfl
  have h := X.exp_upper (toGQ !![a, b; 0, d]) (by rw [e]; simp) f r
  simpa [e] using h

end GlobalTheory.KZ
