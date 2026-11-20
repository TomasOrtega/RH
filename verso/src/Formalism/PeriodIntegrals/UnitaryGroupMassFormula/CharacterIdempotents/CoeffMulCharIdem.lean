import Mathlib
import Formalism.PeriodIntegrals.CharIdem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Central

open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Simplify using `[act, MonoidAlgebra.lift_single]`.
-/
theorem act_single (W : FDRep ℂ G) (g : G) (r : ℂ) :
    act W (MonoidAlgebra.single g r) = r • W.ρ g := by
  simp [act, MonoidAlgebra.lift_single]

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_on with`. Consider the case `of g`. Rewrite using `[MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, coeff_charIdem, act_single]`. Simplify using `only [one_smul, mul_inv_rev, inv_inv, one_mul]`. Rewrite using `[← map_mul, FDRep.character]`.

Consider the case `add x y hx hy`. Rewrite using `[add_mul, map_add, mul_add, map_add, mul_add, ← hx, ← hy]`. Both sides reduce to the same expression. Consider the case `smul r x hx`. Rewrite using `[smul_mul_assoc, map_smul, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm, ← hx]`.

Both sides reduce to the same expression.
-/
theorem coeff_mul_charIdem (W : FDRep ℂ G) (x : MonoidAlgebra ℂ G) (h : G) :
    (x * charIdem W).coeff h =
      ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ)) *
        LinearMap.trace ℂ W (W.ρ h⁻¹ * act W x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, coeff_charIdem, act_single]
    simp only [one_smul, mul_inv_rev, inv_inv, one_mul]
    rw [← map_mul, FDRep.character]
  | add x y hx hy =>
    rw [add_mul, map_add, mul_add, map_add, mul_add, ← hx, ← hy]
    rfl
  | smul r x hx =>
    rw [smul_mul_assoc, map_smul, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm, ← hx]
    rfl

/- English proof (translation)
Introduce `G _ _ V W hV hW`. Prove the components needed by the constructor for the conclusion. Introduce `hVW`. Establish `h1 : act W (charIdem V) = 1` using `((hS G V W hV hW).1 hVW)`. Use extensionality with `h`.

Rewrite using `[coeff_mul_charIdem, h1, mul_one, coeff_charIdem, FDRep.character]`. Introduce `hVW`. Establish `h0 : act W (charIdem V) = 0` using `((hS G V W hV hW).2 hVW)`. Use extensionality with `h`. Rewrite using `[coeff_mul_charIdem, h0, mul_zero, map_zero, mul_zero]`.

Both sides reduce to the same expression.
-/
theorem mulEq_of (hS : Scalar) : MulEq := by
  intro G _ _ V W hV hW
  constructor
  · intro hVW
    have h1 : act W (charIdem V) = 1 := ((hS G V W hV hW).1 hVW)
    ext h
    rw [coeff_mul_charIdem, h1, mul_one, coeff_charIdem, FDRep.character]
  · intro hVW
    have h0 : act W (charIdem V) = 0 := ((hS G V W hV hW).2 hVW)
    ext h
    rw [coeff_mul_charIdem, h0, mul_zero, map_zero, mul_zero]
    rfl

end PI.CharIdemW
