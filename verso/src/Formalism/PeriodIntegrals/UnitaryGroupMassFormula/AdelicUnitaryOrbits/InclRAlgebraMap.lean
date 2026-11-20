import Mathlib
import Formalism.PeriodIntegrals.AdelicOrbitU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

/- English proof (translation)
Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
lemma isHerm_JR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) :
    Formalism.UG.IsHerm (sigR R σ) (JR R J) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, JR, sigR_inclR, hJ]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma isUnit_det_JR (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) : IsUnit (JR (F := F) R J).det := by
  have h : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (isUnit_iff_ne_zero.mpr hJ).map _

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
lemma hform_incl (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (v i)) (fun i => inclR R (w i)) =
      inclR R (hE σ J v w) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma inclR_algebraMap (R : Type) [CommRing R] [Algebra F R] (b : F) :
    inclR R (algebraMap F E b) = algebraMap F (R ⊗[F] E) b :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes b

end SlopeTestRemainingChoices

end PIW.AdelicOrbitU
