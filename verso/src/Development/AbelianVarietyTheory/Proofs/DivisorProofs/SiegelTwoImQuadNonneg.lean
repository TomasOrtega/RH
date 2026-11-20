import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `hP : (T.map Complex.im).PosDef` using `hT.2`. Establish `hs : ∀ a c, (T a c).im = (T c a).im`. Introduce `a c`. Use `congrFun (congrFun hP.isHermitian c) a` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`.

Establish `hq : ∀ v : Fin g → ℝ, 0 ≤ ∑ a, ∑ c, (T a c).im * (v a * v c)`. Introduce `v`. Use `hP.posSemidef.dotProduct_mulVec_nonneg v` as an intermediate fact. Simplify using `only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum] at this`. Use `this.trans_eq ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Establish `h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im = ∑ a, ∑ c, 2 * (T a c).im * ((x a).re * (x c).im) - ∑ a, ∑ c, 2 * (T a c).im * ((x a).im * (x c).re)`. Rewrite using `[← Finset.sum_sub_distrib, Complex.im_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_sub_distrib, Complex.im_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, sub_eq_zero, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hs c a]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re = 2 * (∑ a, ∑ c, (T a c).im * ((x a).re * (x c).re)) + 2 * ∑ a, ∑ c, (T a c).im * ((x a).im * (x c).im)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Use `hq fun a => (x a).re` as an intermediate fact. Use `hq fun a => (x a).im` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem siegel_two_im_quad_nonneg {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T)
    (x : Fin g → ℂ) :
    (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im = 0 ∧
    0 ≤ (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re := by
  have hP : (T.map Complex.im).PosDef := hT.2
  have hs : ∀ a c, (T a c).im = (T c a).im := by
    intro a c
    have := congrFun (congrFun hP.isHermitian c) a
    simpa [Matrix.conjTranspose_apply] using this
  have hq : ∀ v : Fin g → ℝ, 0 ≤ ∑ a, ∑ c, (T a c).im * (v a * v c) := by
    intro v
    have := hP.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum] at this
    refine this.trans_eq ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  constructor
  · have h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im
        = ∑ a, ∑ c, 2 * (T a c).im * ((x a).re * (x c).im) - ∑ a, ∑ c, 2 * (T a c).im * ((x a).im * (x c).re) := by
      rw [← Finset.sum_sub_distrib, Complex.im_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib, Complex.im_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
      ring
    rw [h1, sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hs c a]; ring
  · have h1 : (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re
        = 2 * (∑ a, ∑ c, (T a c).im * ((x a).re * (x c).re)) + 2 * ∑ a, ∑ c, (T a c).im * ((x a).im * (x c).im) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp
      ring
    rw [h1]
    have := hq fun a => (x a).re
    have := hq fun a => (x a).im
    positivity

end GlobalTheory
