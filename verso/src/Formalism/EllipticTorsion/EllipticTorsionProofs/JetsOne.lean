import Formalism.EllipticTorsion.JetsCube
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupLinearJets

variable {K : Type u} [CommRing K]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]`. Simplify using `[PowerSeries.coeff]`.
-/
theorem constantCoeff_pderiv_unit (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K () f) = coeff 1 f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp [PowerSeries.coeff]

/- English proof (translation)
Establish `h` using `Formalism.G.LogCR.pderiv_psubst (τ := Unit) (a := (a : MvPowerSeries Unit K)) ha φ ()`. Establish `h2` using `congrArg MvPowerSeries.constantCoeff h`. Rewrite `h2` using `[constantCoeff_pderiv_unit, map_mul, constantCoeff_pderiv_unit]`. Rewrite using `[h2]`. Use `congr 1`.

Rewrite using `[PowerSeries.subst_def, Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) _ (fun _ => ha)]`. Use `show PowerSeries.constantCoeff (PowerSeries.derivative K φ) = _`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]`. Simplify using the standard rewrite rules.
-/
theorem coeff_one_subst {φ a : PowerSeries K} (ha : constantCoeff a = 0) :
    coeff 1 (φ.subst a) = coeff 1 φ * coeff 1 a := by
  have h := Formalism.G.LogCR.pderiv_psubst (τ := Unit) (a := (a : MvPowerSeries Unit K)) ha φ ()
  have h2 := congrArg MvPowerSeries.constantCoeff h
  rw [constantCoeff_pderiv_unit, map_mul, constantCoeff_pderiv_unit] at h2
  rw [h2]
  congr 1
  rw [PowerSeries.subst_def,
    Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) _ (fun _ => ha)]
  show PowerSeries.constantCoeff (PowerSeries.derivative K φ) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp

end Formalism.ELL.FormalGroupLinearJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupLinearJets

/- English proof (translation)
Introduce `K _ _ _ F φ a n ha hG`. Establish `hP` using `hN K Unit _ hG ()`. Establish `h0` using `hP 0`. Rewrite `h0` using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pderiv_unit, map_sub, coeff_one_subst ha.1, map_smul, smul_eq_mul]`. Establish `hD : constantCoeff (invD F φ) = coeff 1 φ`.

Establish `hw : constantCoeff (omegaF F) = 1` using `Formalism.G.LogP.constantCoeff_omega (FK F)`. Rewrite using `[invD, map_mul, hw, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]`. Simplify using the standard rewrite rules. Rewrite using `[hD]`. Use `h0 using 2` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jetsOne_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsOne.{u} := by
  intro K _ _ _ F φ a n ha hG
  have hP := hN K Unit _ hG ()
  have h0 := hP 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pderiv_unit, map_sub,
    coeff_one_subst ha.1, map_smul, smul_eq_mul] at h0
  have hD : constantCoeff (invD F φ) = coeff 1 φ := by
    have hw : constantCoeff (omegaF F) = 1 := Formalism.G.LogP.constantCoeff_omega (FK F)
    rw [invD, map_mul, hw, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative]
    simp
  rw [hD]
  convert h0 using 2
  ring

end Formalism.ELL
