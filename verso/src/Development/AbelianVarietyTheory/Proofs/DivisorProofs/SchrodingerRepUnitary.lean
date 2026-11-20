import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
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
