import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

open Formalism.MainNotions.GL3Theta in

/- English proof (translation)
Introduce `p _ g`. Use `set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef`. Establish `hL0 : MvPowerSeries.constantCoeff L = 0`. Rewrite using `[hLdef, GL3Theta.G1.lg]`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)`.

Establish `hL : PowerSeries.HasSubst L` using `PowerSeries.HasSubst.of_constantCoeff_zero hL0`. Establish `key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p], MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d))`. Introduce `e`. Establish `hfin` using `PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e`. Establish `hfin' : (Function.support fun d : ℕ => PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite` using `hfin`.

Use `⟨hfin'.toFinset, fun c => ?_⟩` and prove the remaining obligations. Establish `ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0`. Simplify using `[hL0]`. Establish `ha : PowerSeries.HasSubst (MvPowerSeries.C c * L)` using `PowerSeries.HasSubst.of_constantCoeff_zero ha0`. Use `show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _`.

Rewrite using `[PowerSeries.coeff_subst ha]`. Establish `hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) = PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d))`. Introduce `d`. Rewrite using `[mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]`. Repeatedly rewrite using `[hterm]`.

Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `d hd`. Rewrite `hd` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]`. Introduce `h0`.

Apply `hd` to reduce the goal to its premises. Simplify using `only [PowerSeries.coeff_mk, one_smul] at h0`. Rewrite using `[h0, mul_zero, mul_zero]`. Establish `hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} = ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] | ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1}`. Use extensionality with `c`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Both sides reduce to the same expression. Rewrite using `[hset]`. Use `isClosed_iInter fun e => ?_` and prove the remaining obligations. Take `⟨S, hS⟩` from `key e`.

Establish `hfun : (fun c : ℂ_[p] => MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) = fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d))`. Use function extensionality and compare the values at `hS`. Establish `hcont : Continuous fun c : ℂ_[p] => MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])`. Rewrite using `[hfun]`. Use `fun_prop`.

Conclude with `isClosed_le (continuous_norm.comp hcont) continuous_const`.
-/
theorem mulBy_integral_isClosed : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsClosed {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} := by
  intro p _ g
  set L : MvPowerSeries Unit ℂ_[p] := g.lg (GL3Theta.Xv ()) with hLdef
  have hL0 : MvPowerSeries.constantCoeff L = 0 := by
    rw [hLdef, GL3Theta.G1.lg]
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) _
      (GlobalTheory.GenusOneDatum.constantCoeff_flog _ _)
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  have key : ∀ e : Unit →₀ ℕ, ∃ S : Finset ℕ, ∀ c : ℂ_[p],
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) =
        ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
    intro e
    have hfin := PowerSeries.coeff_subst_finite hL (PowerSeries.mk fun _ => (1 : ℂ_[p])) e
    have hfin' : (Function.support fun d : ℕ =>
        PowerSeries.coeff d (PowerSeries.mk fun _ => (1 : ℂ_[p])) • MvPowerSeries.coeff e (L ^ d)).Finite := hfin
    refine ⟨hfin'.toFinset, fun c => ?_⟩
    have ha0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * L) = 0 := by
      simp [hL0]
    have ha : PowerSeries.HasSubst (MvPowerSeries.C c * L) :=
      PowerSeries.HasSubst.of_constantCoeff_zero ha0
    show MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.C c * L) g.ex) = _
    rw [PowerSeries.coeff_subst ha]
    have hterm : ∀ d : ℕ, PowerSeries.coeff d g.ex • MvPowerSeries.coeff e ((MvPowerSeries.C c * L) ^ d) =
        PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) := by
      intro d
      rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, smul_eq_mul]
    simp_rw [hterm]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro h0
    apply hd
    simp only [PowerSeries.coeff_mk, one_smul] at h0
    rw [h0, mul_zero, mul_zero]
  have hset : {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} =
      ⋂ e : Unit →₀ ℕ, {c : ℂ_[p] |
        ‖MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])‖ ≤ 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [hset]
  refine isClosed_iInter fun e => ?_
  obtain ⟨S, hS⟩ := key e
  have hfun : (fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])) =
      fun c => ∑ d ∈ S, PowerSeries.coeff d g.ex * (c ^ d * MvPowerSeries.coeff e (L ^ d)) :=
    funext hS
  have hcont : Continuous fun c : ℂ_[p] =>
      MvPowerSeries.coeff e (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    rw [hfun]
    fun_prop
  exact isClosed_le (continuous_norm.comp hcont) continuous_const

end GlobalTheory
