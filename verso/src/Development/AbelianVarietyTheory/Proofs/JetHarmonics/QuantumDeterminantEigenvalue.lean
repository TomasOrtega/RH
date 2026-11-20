import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperatorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransportStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `x _ hx`. Rewrite using `[Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

/- English proof (translation)
Introduce `hyp k r ε mu R hR Q E hQ hE Y w`. Establish `hK : PI.KFinSmooth` using `hyp.1.2.2.1`. Establish `hC` using `hyp.2.2.1`. Take `⟨hmu, Q0, hQ0, hDS⟩` from `id hR`. Establish `hU0 : IsUnit Q0` using `hQ0.1.1`.

Take `⟨E0, hE0, hgl⟩` from `GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0`. Take `⟨hsm, hd⟩` from `GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0`. Take `⟨-, hexp, -⟩` from `GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0`. Establish `hdQ : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).1 hQ`. Establish `hdQ0 : IsUnit Q0.det` using `(Matrix.isUnit_iff_isUnit_det Q0).1 hU0`.

Establish `hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹)`. Use function extensionality and compare the values at `a b`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[hE a b v, hexp]`. Establish `h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ = (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹)`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h1]`. Simplify using `only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]`. Establish `h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]`.

Establish `h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]`. Rewrite using `[hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h4` using `GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0 (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w`.

Rewrite using `[← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]`. Both sides reduce to the same expression.
-/
theorem qdet_smooth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
