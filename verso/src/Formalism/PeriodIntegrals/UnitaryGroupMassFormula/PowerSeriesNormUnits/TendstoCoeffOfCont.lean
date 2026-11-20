import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul

noncomputable section

open Classical Filter Topology MvPowerSeries.WithPiTopology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section Calc

variable (hE : CalcEquiv)
include hE

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sRefl {σ : Type} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := (hE p σ f f f f).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sOfEq {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : f = g) : Simeq f g := h ▸ sRefl hE f

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sSymm {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f :=
  (hE p σ f g f f).2.1 h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sTrans {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g k) : Simeq f k :=
  (hE p σ f g k f).2.2.1 h1 h2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sAdd {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := (hE p σ f g h k).2.2.2.1 h1 h2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sNeg {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) : Simeq (-f) (-g) :=
  (hE p σ f g f f).2.2.2.2.1 h1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sSub {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f - h) (g - k) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact sAdd hE h1 (sNeg hE h2)

end Calc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem int_X {σ : Type*} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem coeff_subst_sum {τ : Type*} (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simp [ha]) (by omega),
    smul_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem cont_subst {τ : Type*} (G : ℂ_[p] → MvPowerSeries τ ℂ_[p])
    (hG : Continuous G) (h0 : ∀ x, MvPowerSeries.constantCoeff (G x) = 0) (f : PowerSeries ℂ_[p]) :
    Continuous fun x => (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p]) := by
  refine continuous_pi fun e => ?_
  change Continuous fun x => MvPowerSeries.coeff e (PowerSeries.subst (G x) f : MvPowerSeries τ ℂ_[p])
  simp_rw [coeff_subst_sum _ (h0 _), smul_eq_mul]
  refine continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  exact (continuous_coeff ℂ_[p] e).comp (hG.pow d)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tendsto_coeff_of_cont {τ : Type*} (F : ℂ_[p] → MvPowerSeries τ ℂ_[p]) (hF : Continuous F)
    {u : ℕ → ℂ_[p]} {c : ℂ_[p]} (hu : Tendsto u atTop (𝓝 c)) (e : τ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F (u k))) atTop (𝓝 (MvPowerSeries.coeff e (F c))) :=
  (((continuous_coeff ℂ_[p] e).comp hF).tendsto c).comp hu

section Lin

variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)

include hex0 hinv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cont_mulBy {τ : Type*} (y : MvPowerSeries τ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => mulBy l ex c y :=
  cont_subst (fun c => MvPowerSeries.C c * PowerSeries.subst y l) (continuous_C.mul continuous_const)
    (fun c => by rw [map_mul, constantCoeff_subst_log hex0 hinv y hy, mul_zero]) ex

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem cont_be {τ : Type*} (ph : PowerSeries ℂ_[p]) (z y : MvPowerSeries τ ℂ_[p])
    (hz : MvPowerSeries.constantCoeff z = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Continuous fun c : ℂ_[p] => be l ex ph z (mulBy l ex c y) := by
  have hA : Continuous fun c : ℂ_[p] => add l ex z (mulBy l ex c y) := by
    have : (fun c : ℂ_[p] => add l ex z (mulBy l ex c y)) = fun c =>
        PowerSeries.subst (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) ex := by
      funext c; unfold add; rw [L_mulBy hex0 hinv c y hy]
    rw [this]
    exact cont_subst (fun c : ℂ_[p] => PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l)
      (continuous_const.add (continuous_C.mul continuous_const))
      (fun c => by
        show MvPowerSeries.constantCoeff (PowerSeries.subst z l + MvPowerSeries.C c * PowerSeries.subst y l) = 0
        rw [map_add, map_mul, constantCoeff_subst_log hex0 hinv y hy, constantCoeff_subst_log hex0 hinv z hz]; simp) ex
  unfold be
  refine ((cont_subst _ hA (fun c => constantCoeff_formalAdd hex0 hinv _ _ hz (constantCoeff_formalSMul hex0 hinv c y hy)) ph).sub
    continuous_const).sub ?_
  exact cont_subst _ (cont_mulBy hex0 hinv y hy) (fun c => constantCoeff_formalSMul hex0 hinv c y hy) ph

end Lin

end PI.PhNormUnits.UnitaryGroupMassFormula
