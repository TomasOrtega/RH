import Mathlib
import Lemmata.CofiniteContinuousBounds.LeOfCofinite

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => simp [lineHom]`. Consider the case `add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]`.

Simplify using `[lineHom]`.
-/
theorem eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
