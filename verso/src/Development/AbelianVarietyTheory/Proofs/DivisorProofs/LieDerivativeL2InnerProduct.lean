import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def expGL (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp (t • Matrix.of X)).unit

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem expGL_val (X : Lie E a) (t : ℝ) :
    ((expGL X t : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = NormedSpace.exp (t • Matrix.of X) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expGL_zero (X : Lie E a) : expGL X 0 = 1 :=
  Units.ext (by rw [expGL_val, zero_smul, NormedSpace.exp_zero]; rfl)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem expGL_add (X : Lie E a) (s t : ℝ) : expGL X (s + t) = expGL X s * expGL X t := by
  apply Units.ext
  rw [Units.val_mul, expGL_val, expGL_val, expGL_val, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem hasDerivAt_expGL (X : Lie E a) : HasDerivAt (fun t => toL (expGL X t).val) X 0 := by
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasDerivAt_along (X : Lie E a) (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun s => ψ.1 (g * infGL E a (expGL X s)))
      ((lie E a X ψ).1 (g * infGL E a (expGL X t))) t := by
  have h := hasDerivAt_curve ψ (g * infGL E a (expGL X t)) (expGL X) X (expGL_zero X) (hasDerivAt_expGL X)
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h)
  have e : (fun s => ψ.1 (g * infGL E a (expGL X s))) =
      fun x => ψ.1 (g * infGL E a (expGL X t) * infGL E a (expGL X (x - t))) := by
    funext s
    rw [mul_assoc, ← map_mul, ← expGL_add, add_sub_cancel]
  rw [e]
  exact h2

end GlobalTheory.ExpDeriv

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

end GlobalTheory.ExpDeriv

end
