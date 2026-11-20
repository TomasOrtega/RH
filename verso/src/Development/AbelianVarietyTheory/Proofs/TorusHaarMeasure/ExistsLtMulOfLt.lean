import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsomOfGramEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FjNormMulExpLeSupFlow
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedModes

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Break down `ha.eq_or_lt with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `⟨1 / 2, by norm_num, by norm_num, by simpa using hs⟩`. Establish `hm : max s 0 < a` using `max_lt hs h`. Establish `h0 : 0 ≤ max s 0` using `le_max_right _ _`.

Establish `h1 : s ≤ max s 0` using `le_max_left _ _`. Use `⟨(max s 0 + a) / (2 * a), by positivity, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[div_lt_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (max s 0 + a) / (2 * a) * a = (max s 0 + a) / 2` using `by field_simp`.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_lt_mul_of_lt {s a : ℝ} (ha : 0 ≤ a) (hs : s < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ s < θ * a := by
  rcases ha.eq_or_lt with h | h
  · subst h
    exact ⟨1 / 2, by norm_num, by norm_num, by simpa using hs⟩
  · have hm : max s 0 < a := max_lt hs h
    have h0 : 0 ≤ max s 0 := le_max_right _ _
    have h1 : s ≤ max s 0 := le_max_left _ _
    refine ⟨(max s 0 + a) / (2 * a), by positivity, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]
      linarith
    · have : (max s 0 + a) / (2 * a) * a = (max s 0 + a) / 2 := by field_simp
      rw [this]
      linarith

/- English proof (translation)
Introduce `r X la F ps a hF hps ha hmean ξ hξ ν hν x hx`. Take `⟨θ, hθ0, hθ1, hνθ⟩` from `exists_lt_mul_of_lt ha hν`. Conclude with `ModeDecay.fj_eq_zero_of_decay fj_norm_mul_exp_le_sup_flow ClosedDiscontinuity.propDisc_and_la1GG.2 r X la F (θ * a) hF (pnorm_le_exp_neg_tt_near_cusp (MajNear.maj_near_orth MajorantContinuity.majorant_continuity.1) maj_lact_rmul NormFactor.nfac_transform r X la F ps a hF hps ha h …`.
-/
theorem modeHalf_closed : (∀ (r : ℕ) (X : Data E r), ModeHalfStatement X) := by
  intro r X la F ps a hF hps ha hmean ξ hξ ν hν x hx
  obtain ⟨θ, hθ0, hθ1, hνθ⟩ := exists_lt_mul_of_lt ha hν
  exact ModeDecay.fj_eq_zero_of_decay fj_norm_mul_exp_le_sup_flow
    ClosedDiscontinuity.propDisc_and_la1GG.2 r X la F (θ * a) hF
    (pnorm_le_exp_neg_tt_near_cusp
      (MajNear.maj_near_orth MajorantContinuity.majorant_continuity.1) maj_lact_rmul
      NormFactor.nfac_transform r X la F ps a hF hps ha hmean θ (θ * a) hθ0 hθ1 rfl)
    ξ hξ ν hνθ x hx

end GlobalTheory.ClosedModes
