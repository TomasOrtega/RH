import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.LogInv

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]
variable {σ τ υ : Type*}

/- English proof (translation)
Rewrite using `[rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]`. Simplify using `only [rename_eq_subst]`.
-/
theorem rename_subst' (e : σ ↪ τ) {a : υ → MvPowerSeries σ ℂ_[p]} (ha : HasSubst a)
    (f : MvPowerSeries υ ℂ_[p]) :
    rename e (subst a f) = subst (fun s => rename e (a s)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply ha (HasSubst.X_comp e)]
  simp only [rename_eq_subst]

/- English proof (translation)
Rewrite using `[rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hb]`. Simplify using `only [Function.comp_apply, subst_X hb]`.
-/
theorem subst_rename' (e : σ ↪ τ) {b : τ → MvPowerSeries υ ℂ_[p]} (hb : HasSubst b)
    (f : MvPowerSeries σ ℂ_[p]) :
    subst b (rename e f) = subst (fun w => b (e w)) f := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hb]
  simp only [Function.comp_apply, subst_X hb]

/- English proof (translation)
Rewrite using `[PowerSeries.subst, rename_subst' e hg.const]`. Both sides reduce to the same expression.
-/
theorem rename_psubst (e : σ ↪ τ) {g : MvPowerSeries σ ℂ_[p]} (hg : PowerSeries.HasSubst g)
    (f : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst g f) = PowerSeries.subst (rename e g) f := by
  rw [PowerSeries.subst, rename_subst' e hg.const]
  rfl

/- English proof (translation)
Rewrite using `[phiA, phiA, map_mul, rename_C, rename_psubst e (PowerSeries.HasSubst.X w), rename_X]`.
-/
theorem rename_phiA [Finite σ] [Finite τ] (e : σ ↪ τ) (c : ℂ_[p]) (w : σ) :
    rename e (phiA p c w) = phiA p c (e w) := by
  rw [phiA, phiA, map_mul, rename_C, rename_psubst e (PowerSeries.HasSubst.X w), rename_X]

/- English proof (translation)
Rewrite using `[subst_rename' e (hs_phiA p c), rename_subst' e (hs_phiA p c)]`. Simplify using `only [rename_phiA]`.
-/
theorem phi_rename [Finite σ] [Finite τ] (e : σ ↪ τ) (c : ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]) :
    subst (phiA p c) (rename e f) = rename e (subst (phiA p c) f) := by
  rw [subst_rename' e (hs_phiA p c), rename_subst' e (hs_phiA p c)]
  simp only [rename_phiA]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [monomial_zero_one]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, monomial_mul_monomial, one_mul]`.
-/
theorem prod_monomial_one {ι : Type*} (s : Finset ι) (d : ι → τ →₀ ℕ) :
    ∏ i ∈ s, monomial (d i) (1 : ℂ_[p]) = monomial (∑ i ∈ s, d i) 1 := by
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, monomial_mul_monomial, one_mul]

end PI.OrbJet.AO

end
