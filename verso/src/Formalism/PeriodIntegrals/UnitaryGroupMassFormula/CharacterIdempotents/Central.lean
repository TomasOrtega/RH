import Mathlib
import Formalism.PeriodIntegrals.CharIdem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Development

open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Unfold `PI.CharIdem.charIdem`. Simplify using `[Finsupp.single_apply]`.
-/
theorem coeff_charIdem (V : FDRep ℂ G) (g : G) :
    (charIdem V).coeff g =
      ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹ := by
  classical
  unfold PI.CharIdem.charIdem
  simp [Finsupp.single_apply]

/- English proof (translation)
Unfold `PI.CharIdem.charIdem`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Simplify using `only [MonoidAlgebra.single_mul_single, mul_one, one_mul]`. Set `e : G ≃ G` to `⟨fun g => h⁻¹ * g * h, fun g => h * g * h⁻¹, fun g => by group, fun g => by group⟩`. Use `Fintype.sum_equiv e _ _ (fun g => ?_)` and prove the remaining obligations.

Establish `he : h * e g = g * h` using `by show h * (h⁻¹ * g * h) = g * h group`. Establish `hi : (e g)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹` using `by show (h⁻¹ * g * h)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹ group`. Rewrite using `[he, hi, FDRep.char_conj]`.
-/
private theorem charIdem_mul_single_one_comm (V : FDRep ℂ G) (h : G) :
    PI.CharIdem.charIdem V * MonoidAlgebra.single h (1 : ℂ) = MonoidAlgebra.single h (1 : ℂ) * PI.CharIdem.charIdem V := by
  unfold PI.CharIdem.charIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
  let e : G ≃ G := ⟨fun g => h⁻¹ * g * h, fun g => h * g * h⁻¹, fun g => by group, fun g => by group⟩
  refine Fintype.sum_equiv e _ _ (fun g => ?_)
  have he : h * e g = g * h := by
    show h * (h⁻¹ * g * h) = g * h
    group
  have hi : (e g)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹ := by
    show (h⁻¹ * g * h)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹
    group
  rw [he, hi, FDRep.char_conj]

/- English proof (translation)
Use `MonoidAlgebra.induction_on (motive := fun y => PI.CharIdem.charIdem V * y = y * PI.CharIdem.charIdem V) x ?_ ?_ ?_` and prove the remaining obligations. Introduce `g`. Simplify `charIdem_mul_single_one_comm V g` using `[MonoidAlgebra.of_apply]`. Introduce `a b ha hb`. Rewrite using `[mul_add, add_mul, ha, hb]`.

Introduce `r a ha`. Rewrite using `[mul_smul_comm, smul_mul_assoc, ha]`.
-/
theorem idempotent_mul_comm (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G) :
    charIdem V * x = x * charIdem V := by
  refine MonoidAlgebra.induction_on (motive := fun y => PI.CharIdem.charIdem V * y = y * PI.CharIdem.charIdem V) x ?_ ?_ ?_
  · intro g
    simpa [MonoidAlgebra.of_apply] using charIdem_mul_single_one_comm V g
  · intro a b ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro r a ha
    rw [mul_smul_comm, smul_mul_assoc, ha]

/- English proof (translation)
Introduce `G _ _ V x`. Conclude with `idempotent_mul_comm V x`.
-/
theorem central : Central := by
  intro G _ _ V x
  exact idempotent_mul_comm V x

end PI.CharIdemW
