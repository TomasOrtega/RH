import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gN_nonneg_bessel_integrability {k r : ℕ} (x : Formalism.FourierDecayAlt.B.Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN x := Real.sqrt_nonneg _

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gN_eq_one_of_zero_dim (x : Formalism.FourierDecayAlt.B.Mat 0 0) (hx : x ∈ UH (Hpk 0 0)) : Formalism.FourierDecayAlt.B.gN x = 1 := by
  have h := congrFun (congrFun (show xᴴ * Hpk 0 0 * x = Hpk 0 0 from hx) 0) 0
  simp [Matrix.mul_apply, Hpk, Fin.sum_univ_succ] at h
  have h1 : Complex.normSq (x 0 0) = 1 := by
    have h4 : ((Complex.normSq (x 0 0) : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self, h]
    exact_mod_cast h4
  unfold Formalism.FourierDecayAlt.B.gN
  simp [Fin.sum_univ_succ, h1]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem integrable_gN_rpow_of_lintegral_lt_top {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ}
    (h : (∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) ∂μ) < ∞) :
    Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) μ := by
  have hmeas : Measurable fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A) := by
    unfold Formalism.FourierDecayAlt.B.gN
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)).2 h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem growth_group_bound : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  intro k r μG A hG hA
  have hG' : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r) μG :=
    Formalism.MainNotions.BridgeLemma₃.hu_haarG k r μG ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2⟩
  rcases Nat.eq_zero_or_pos (k + r) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : k = 0 ∧ r = 0 := by omega
    have h1 := Formalism.FourierDecayAlt.P.norm_power_integrable_sharp 0 0 μG 1 hG' (by simp [Formalism.FourierDecayAlt.B.AB])
    have hI := integrable_gN_rpow_of_lintegral_lt_top h1
    refine hI.congr ?_
    have hconc : μG {x : Mt 0 0 | Matrix.of x ∉ UH (Hpk 0 0)} = 0 := hG.2.2.1
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hconc
    intro hxG
    apply hx
    show Formalism.FourierDecayAlt.B.gN (k := 0) (r := 0) (Matrix.of x) ^ (-(1:ℝ)) =
      Formalism.FourierDecayAlt.B.gN (k := 0) (r := 0) (Matrix.of x) ^ (-A)
    rw [gN_eq_one_of_zero_dim (Matrix.of x : Formalism.FourierDecayAlt.B.Mat 0 0) hxG, Real.one_rpow, Real.one_rpow]
  · have hAB : Formalism.FourierDecayAlt.B.AB k r ≤ A := by
      have hkr : (1 : ℝ) ≤ (k : ℝ) + r := by exact_mod_cast hpos
      simp only [Formalism.FourierDecayAlt.B.AB, Formalism.FourierDecayAlt.ThreeDimData.AG] at hA ⊢
      nlinarith
    exact integrable_gN_rpow_of_lintegral_lt_top (Formalism.FourierDecayAlt.P.norm_power_integrable_sharp k r μG A hG' hAB)

end Formalism.FourierDecayAlt.P
