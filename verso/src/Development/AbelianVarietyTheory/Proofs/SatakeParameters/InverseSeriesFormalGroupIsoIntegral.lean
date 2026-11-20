import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe

noncomputable section

namespace GlobalTheory.InverseSeriesIntegral

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.KerInert.BeCob (vLT eLT)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

/- English proof (translation)
Establish `hex` using `hOk.2.2.1`. Establish `hinv` using `hOk.2.2.2`. Use `set e := eLT hLT with he`. Establish `he1 : ‖e‖ = 1` using `Formalism.L2.G.Pend.norm_wToC_unit l _`. Establish `hene : e ≠ 0` using `by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1`.

Use `set th0 := Formalism.L2.G.Pend.thOf hLT with hth0`. Establish `h00 : PowerSeries.constantCoeff th0 = 0` using `Formalism.L2.G.Pend.thOf_zero hLT`. Establish `hu : IsUnit (PowerSeries.coeff 1 th0)` using `Formalism.L2.G.Pend.thOf_unit hLT`. Use `set i0 := th0.substInvOfIsUnit hu with hi0`. Establish `hi00 : PowerSeries.constantCoeff i0 = 0` using `PowerSeries.constantCoeff_substInvOfIsUnit _ _`.

Establish `hR : PowerSeries.subst i0 th0 = PowerSeries.X` using `PowerSeries.subst_substInvOfIsUnit_right _ h00 hu`. Use `set thC := PowerSeries.map (wToC l) th0 with hthC`. Use `set iC := PowerSeries.map (wToC l) i0 with hiC`. Establish `hthC0 : PowerSeries.constantCoeff thC = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]`.

Establish `hiC0 : PowerSeries.constantCoeff iC = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]`. Establish `hRC : PowerSeries.subst iC thC = PowerSeries.X`. Establish `h` using `congrArg (MvPowerSeries.map (wToC l)) hR`. Rewrite `h` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)]`.

Conclude with `h.trans (MvPowerSeries.map_X _ _)`. Establish `hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0`. Rewrite using `[map_mul, cc_lgF', mul_zero]`. Establish `hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l`. Establish `h` using `Formalism.L2.G.Pend.thOf_log hLT`.

Rewrite `h` using `[lgF_eq_logF]`. Conclude with `h`. Establish `hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X`. Unfold `vLT`. Rewrite using `[PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0) (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]`.

Establish `e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l`. Rewrite using `[← mul_assoc]`. Use `show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l`. Rewrite using `[← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]`. Rewrite using `[e1]`.

Conclude with `Formalism.L2.G.Pend.ex_l g hex hinv`. Use `⟨i0, ?_⟩` and prove the remaining obligations. Use `show iC = vLT hLT`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (Formalism.MainNotions.FormalGroupSystem.WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

/- English proof (translation)
Introduce `l _ g hOk hLT n`. Take `⟨w, hw⟩` from `exists_witt_series_inverse_formalGroup_iso hOk hLT`. Rewrite using `[← hw, PowerSeries.coeff_map]`. Use `Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)` as an intermediate fact. Simplify using `using this`.
-/
theorem v_integral : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  intro l _ g hOk hLT n
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

end GlobalTheory.InverseSeriesIntegral
