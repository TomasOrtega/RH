import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsFSDensity
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP
open scoped Matrix

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_halfLogPot_eq (N : ℕ) (z : Fin N → ℂ) :
    hessC (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
      (Real.pi : ℂ) • chernCoeff 0 z := by
  have h : (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) =
      fun y => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot y := rfl
  rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0,
    smul_smul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the signs of the components of the expression. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Both sides reduce to the same expression.
-/
theorem FubiniStudyChartDensity.proof : FubiniStudyChartDensity.Statement := by
  intro N z w
  constructor
  · have h := ReciprocityTheory.AnForm.M.re_star_dot_hessC
      (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z (star w)
    have h' := ReciprocityTheory.AnForm.M.re_star_dot_hessC (HilbertSamuel.ProjFS.logPot (N := N)) z (star w)
    rw [star_star] at h h'
    have hl := HilbertSamuel.ProjFS.levi_logPot_nonneg z w
    have hH : hessC (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
        ((1 / 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z :=
      ReciprocityTheory.AnForm.M.hessC_const_mul' (1 / 2) HilbertSamuel.ProjFS.logPot z
    rw [← h, hH, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, h']
    positivity
  · unfold maDens
    rw [ReciprocityTheory.AnForm.A.mdisc_const, hessC_halfLogPot_eq, Matrix.det_smul, Fintype.card_fin,
      det_chernCoeff, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hS := one_add_normSqSum_pos z
    have hpi := Real.pi_pos
    change (N.factorial : ℝ) * (2 / Real.pi) ^ N *
        (Real.pi ^ N * ((1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1))) = _
    rw [div_pow, div_pow, one_pow, mul_pow]
    field_simp
    rfl

end GroundTheory.Heights₂.Heights.FourB
