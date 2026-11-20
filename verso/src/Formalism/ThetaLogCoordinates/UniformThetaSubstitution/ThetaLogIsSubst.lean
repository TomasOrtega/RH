import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOneK
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ThetaLogIsSubstitution
import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementN

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

/- English proof (translation)
Introduce `K _ ν r0 r1 _ om oms ϖ μ Tht hμ`. Establish `hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0`. Introduce `x`. Unfold `zLin`. Rewrite using `[map_sum]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `s _`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x)` using `fun x => PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)`. Establish `hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0`.

Introduce `x`. Unfold `sSub`. Rewrite using `[PowerSeries.constantCoeff_subst (hz x)]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`.

Break down `d with _ | d` into its components or cases. Simplify using `[hμ]`. Simplify using `[map_pow, hz0 x]`. Establish `ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])`. Establish `hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)`.

Conclude with `MvPowerSeries.subst_comp_subst_apply ha hb Tht`.
-/
theorem thetaLogIsSubst : ThetaLogIsSubst := by
  intro K _ ν r0 r1 _ om oms ϖ μ Tht hμ

  have hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
    intro x
    unfold zLin
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs <;> simp
  have hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)

  have hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 := by
    intro x
    unfold sSub
    rw [PowerSeries.constantCoeff_subst (hz x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases d with _ | d
    · simp [hμ]
    · simp [map_pow, hz0 x]
  have ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])
  have hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 =>
      MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)
  exact MvPowerSeries.subst_comp_subst_apply ha hb Tht

end Formalism.InvariantFactorPaths.G7.Top
