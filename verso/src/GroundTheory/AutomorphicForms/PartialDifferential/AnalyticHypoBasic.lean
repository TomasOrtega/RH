import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticDiffOp

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def dT {k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x ↦ iteratedFDeriv ℝ k f x v

def ev (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

def pd (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x ↦ fderiv ℝ f x (ev i)

def pdT {k : ℕ} (J : Fin k → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  dT (fun l ↦ ev (J l)) f

def hsD (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2)

def l2n (g : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ := (eLpNorm g 2 volume).toReal

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dT_apply {k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    dT v f x = iteratedFDeriv ℝ k f x v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pdT_apply {k : ℕ} (J : Fin k → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    pdT J f x = iteratedFDeriv ℝ k f x (fun l ↦ ev (J l)) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[dT, iteratedFDeriv_zero_apply]`.
-/
theorem dT_zero (v : Fin 0 → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    dT v f = f := by
  funext x
  simp [dT, iteratedFDeriv_zero_apply]

/- English proof (translation)
The claim follows from `dT_zero _ f`.
-/
theorem pdT_zero (J : Fin 0 → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) : pdT J f = f :=
  dT_zero _ f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pderiv_eq_dT (α : Fin n → ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : pderiv α f x = dT (mdir α) f x := rfl

/- English proof (translation)
Simplify using `[ev]`.
-/
theorem norm_ev (i : Fin n) : ‖ev i‖ = 1 := by
  simp [ev]

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsD_nonneg (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ hsD k f x :=
  Real.sqrt_nonneg _

/- English proof (translation)
The claim follows from `Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)`.
-/
theorem hsD_sq (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    hsD k f x ^ 2 = ∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/- English proof (translation)
Rewrite using `[hsD, Fintype.sum_unique, pdT_zero, Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem hsD_zero (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    hsD 0 f x = ‖f x‖ := by
  rw [hsD, Fintype.sum_unique, pdT_zero, Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
The claim follows from `ENNReal.toReal_nonneg`.
-/
theorem l2Norm_nonneg_alt (g : EuclideanSpace ℝ (Fin n) → ℝ) : 0 ≤ l2n g :=
  ENNReal.toReal_nonneg

end

end GroundTheory.Automorphic.Sobolev
