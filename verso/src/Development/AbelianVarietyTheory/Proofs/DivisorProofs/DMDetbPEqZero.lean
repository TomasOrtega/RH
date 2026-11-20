import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntryStatement
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

/- English proof (translation)
Introduce `n ε x`. Set `Mx : Matrix (Fin n) (Fin n) (Poly n)` to `Matrix.of fun a b => X (Sum.inr (a, b))`. Set `W : Matrix (Fin n) (Fin n) (Poly n)` to `(barM ε (Matrix.single x.1.2 x.1.1 1)).map C`. Establish `hD : ∀ i j, dM ε x (Mx i j) = (Mx * W - W * Mx) i j`. Introduce `i j`.

Simplify using `only [dM, dZ, Mx, W, Matrix.of_apply, mkDerivation_X, Sum.elim_inr, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Finset.sum_sub_distrib]`. Apply the tactic sequence `have key := GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry (dM ε x) Mx`. Establish `hdet : detbP n = Mx.det` using `rfl`. Rewrite using `[hdet, key]`. Repeatedly rewrite using `[hD]`.

Establish `htr : ∑ i, ∑ j, Mx.adjugate j i * (Mx * W - W * Mx) i j = Matrix.trace (Mx.adjugate * (Mx * W - W * Mx))`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[htr, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc Mx.adjugate Mx W, Matrix.adjugate_mul, ← Matrix.mul_assoc Mx.adjugate W Mx, Matrix.trace_mul_comm (Mx.adjugate * W) Mx, ← Matrix.mul_assoc Mx Mx.adjugate W, Matrix.mul_adjugate, sub_self]`.
-/
theorem modeDerivation_det_eq_zero : GlobalTheory.PsCo.Cw2a.T_dM_detb := by
  intro n ε x
  let Mx : Matrix (Fin n) (Fin n) (Poly n) := Matrix.of fun a b => X (Sum.inr (a, b))
  let W : Matrix (Fin n) (Fin n) (Poly n) := (barM ε (Matrix.single x.1.2 x.1.1 1)).map C
  have hD : ∀ i j, dM ε x (Mx i j) = (Mx * W - W * Mx) i j := by
    intro i j
    simp only [dM, dZ, Mx, W, Matrix.of_apply, mkDerivation_X, Sum.elim_inr, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_sub_distrib]
  have key := GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry (dM ε x) Mx
  have hdet : detbP n = Mx.det := rfl
  rw [hdet, key]
  simp_rw [hD]
  have htr : ∑ i, ∑ j, Mx.adjugate j i * (Mx * W - W * Mx) i j
      = Matrix.trace (Mx.adjugate * (Mx * W - W * Mx)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
  rw [htr, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc Mx.adjugate Mx W, Matrix.adjugate_mul,
    ← Matrix.mul_assoc Mx.adjugate W Mx, Matrix.trace_mul_comm (Mx.adjugate * W) Mx,
    ← Matrix.mul_assoc Mx Mx.adjugate W, Matrix.mul_adjugate, sub_self]

end GlobalTheory.PsCo.Cw2a
