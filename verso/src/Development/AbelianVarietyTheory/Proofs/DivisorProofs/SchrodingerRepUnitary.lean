import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

/- English proof (translation)
Establish `h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))`. Introduce `x`. Establish `hp : phase w x * starRingEnd ℂ (phase w x) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]`. Simplify using the standard rewrite rules.

Simplify using `only [rhoFun, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hp, one_mul]`. Repeatedly rewrite using `[h]`.

Conclude with `integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)`.
-/
theorem integral_rhoFun_mul_conj (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  have h : ∀ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) =
      u (x + pPart w) * starRingEnd ℂ (v (x + pPart w)) := by
    intro x
    have hp : phase w x * starRingEnd ℂ (phase w x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
      simp
    simp only [rhoFun, map_mul]
    calc _ = (phase w x * starRingEnd ℂ (phase w x)) * (u (x + pPart w) * starRingEnd ℂ (v (x + pPart w))) := by
          ring
      _ = _ := by rw [hp, one_mul]
  simp_rw [h]
  exact integral_add_right_eq_self (fun x => u x * starRingEnd ℂ (v x)) (pPart w)

end GlobalTheory.RealWeil
