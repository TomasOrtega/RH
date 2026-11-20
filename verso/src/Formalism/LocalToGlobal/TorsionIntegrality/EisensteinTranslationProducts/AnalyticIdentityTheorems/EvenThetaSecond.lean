import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

noncomputable section
open scoped BigOperators ComplexConjugate Topology

namespace Formalism.L2.Th1.F

open ThreeTermRelation ThetaZeroHermitianLemmas in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem even_theta_line : ThetaZeroLine := by
  intro L ω₀ F hω hh hF hq
  have hU : ∀ ω ∈ L.lattice, ∀ z, opU L ω F z = thetaZeroCharacter L ω₀ ω * F z := by
    intro ω hωl z
    simp only [opU]
    rw [hq ω hωl z]
    have hinv : Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2
        + (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2) = 0 by ring, Complex.exp_zero]
    linear_combination (thetaZeroCharacter L ω₀ ω * F z) * hinv
  have hlin : ∀ (x a : ℂ) (G : ℂ → ℂ) (z : ℂ), opU L x (fun w => a * G w) z = a * opU L x G z := by
    intro x a G z
    simp only [opU]
    ring
  have hsc : ∀ ω, semiChar L ω * semiChar L ω = 1 := by
    intro ω
    unfold semiChar
    split_ifs <;> norm_num
  have hG : Differentiable ℂ (opU L (-(ω₀ / 2)) F) := by
    first
      | (unfold opU herm
         fun_prop)
      | (unfold opU
         exact (hF.comp (differentiable_id.add_const _)).mul (by unfold herm; fun_prop))
  have hcond : ∀ ω ∈ L.lattice, ∀ z, semiChar L ω * opU L ω (opU L (-(ω₀ / 2)) F) z
      = opU L (-(ω₀ / 2)) F z := by
    intro ω hωl z
    have hfun : opU L ω F = fun w => thetaZeroCharacter L ω₀ ω * F w := funext (hU ω hωl)
    have haltE : altE L ω (-(ω₀ / 2)) = (-1 / 2 : ℝ) * altE L ω ω₀ := by
      have e : -(ω₀ / 2) = (((-1 / 2 : ℝ)) : ℂ) * ω₀ := by
        push_cast
        ring
      rw [e]
      simp only [altE, herm, map_mul, Complex.conj_ofReal]
      rw [show ω * ((((-1 / 2 : ℝ)) : ℂ) * conj ω₀) / (area L : ℂ)
          = (((-1 / 2 : ℝ)) : ℂ) * (ω * conj ω₀ / (area L : ℂ)) by ring]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    obtain ⟨k, hk⟩ := altEInt L ω ω₀ hωl hω
    have hexp : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((((-1 / 2 : ℝ) * (k : ℝ) : ℝ)) : ℂ))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (((k : ℝ)) : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      have e2 : -(2 * (Real.pi : ℂ)) * Complex.I * ((((-1 / 2 : ℝ) * (k : ℝ) : ℝ)) : ℂ)
          + (Real.pi : ℂ) * Complex.I * (((k : ℝ)) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [e2]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [(opUComm L F z).2 ω (-(ω₀ / 2)), hfun, hlin]
    unfold thetaZeroCharacter
    rw [haltE, hk]
    linear_combination (opU L (-(ω₀ / 2)) F z * semiChar L ω * semiChar L ω) * hexp
      + opU L (-(ω₀ / 2)) F z * hsc ω
  obtain ⟨a, ha⟩ := thetaLine L (opU L (-(ω₀ / 2)) F) hG hcond
  have hback : ∀ z, F z = opU L (ω₀ / 2) (opU L (-(ω₀ / 2)) F) z := by
    intro z
    rw [opUMul L (ω₀ / 2) (-(ω₀ / 2)) F z, add_neg_cancel, (opUComm L F z).1]
    have h0alt : altE L (ω₀ / 2) (-(ω₀ / 2)) = 0 := by
      have hherm : herm L (ω₀ / 2) (-(ω₀ / 2)) = ((-(Complex.normSq (ω₀ / 2)) / area L : ℝ) : ℂ) := by
        simp only [herm, map_neg, mul_neg, Complex.mul_conj]
        first
          | (push_cast
             ring)
          | push_cast
          | norm_cast
      simp only [altE, hherm, Complex.ofReal_im]
    rw [h0alt]
    simp
  have hG' : opU L (-(ω₀ / 2)) F = fun w => a * sgStar L w := funext ha
  have hK := (th0Const L (ω₀ / 2)).2 hh
  have hth : ∀ z, opU L (ω₀ / 2) (sgStar L) z
      = th0 L (ω₀ / 2) z * opU L (ω₀ / 2) (sgStar L) 0 := by
    intro z
    simp only [th0]
    first
      | rw [div_mul_cancel₀ _ hK]
      | field_simp
  intro z
  rw [hback z, hback 0, hG', hlin, hlin, hth z]
  ring

end Formalism.L2.Th1.F
