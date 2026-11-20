import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

/- English proof (translation)
Establish `hX : ∀ i j k : σ, MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.X k : MvPolynomial σ R)) = 0`. Introduce `i j k`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[MvPolynomial.pderiv_X_of_ne h]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p k hp`.

Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add, hX, mul_zero, zero_add, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_pderiv_comm {σ R : Type} [CommRing R] (v w : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv v (MvPolynomial.pderiv w f) = MvPolynomial.pderiv w (MvPolynomial.pderiv v f) := by
  have hX : ∀ i j k : σ, MvPolynomial.pderiv i (MvPolynomial.pderiv j (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
    intro i j k
    by_cases h : k = j
    · subst h; simp
    · simp [MvPolynomial.pderiv_X_of_ne h]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hX, mul_zero, zero_add, hp]
    ring

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Conclude with `pderiv_pderiv_comm (R := ℤ) v w f`.
-/
theorem pd_comm {H : Type} {N0 N1 : ℕ} (v w : XZ (Bool × H) N0 N1) :
    Commute (pd (H := H) (N0 := N0) (N1 := N1) v) (pd w) := by
  refine LinearMap.ext fun f => ?_
  exact pderiv_pderiv_comm (R := ℤ) v w f

/- English proof (translation)
Introduce `H N0 N1 t t'`. Unfold `lapT`. Use `Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_` and prove the remaining obligations. Use `Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => ?_` and prove the remaining obligations. Conclude with `((pd_comm _ _).mul_right (pd_comm _ _)).mul_left ((pd_comm _ _).mul_right (pd_comm _ _))`.
-/
theorem pLapComm : PLapComm := by
  intro H N0 N1 t t'
  unfold lapT
  refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
  refine Commute.sum_right _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact ((pd_comm _ _).mul_right (pd_comm _ _)).mul_left ((pd_comm _ _).mul_right (pd_comm _ _))

end PI.EntAtD.W
