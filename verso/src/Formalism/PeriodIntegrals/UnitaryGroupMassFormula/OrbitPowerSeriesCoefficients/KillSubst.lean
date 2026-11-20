import Mathlib

noncomputable section

namespace PI.OrbShared

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {σ τ υ R : Type*} [CommRing R]

/- English proof (translation)
Establish `h : constantCoeff (killCompl e (a s)) = constantCoeff (a s)`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero]`. Rewrite using `[h]`. Conclude with `ha.const_coeff s`. Use `coeff_zero d := by`.

Use `(ha.coeff_zero (Finsupp.embDomain e d)).subset ?_` and prove the remaining obligations. Introduce `s hs`. Simplify `hs` using `[coeff_killCompl]`.
-/
theorem hasSubst_killCompl (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    HasSubst (fun s => killCompl e (a s)) where
  const_coeff s := by
    have h : constantCoeff (killCompl e (a s)) = constantCoeff (a s) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
        coeff_killCompl, Finsupp.embDomain_zero]
    rw [h]; exact ha.const_coeff s
  coeff_zero d := by
    refine (ha.coeff_zero (Finsupp.embDomain e d)).subset ?_
    intro s hs
    simpa [coeff_killCompl] using hs

/- English proof (translation)
Apply `continuous_pi` to reduce the goal to its premises. Introduce `x`. Establish `: (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p`. Use function extensionality and compare the values at `p`. Conclude with `coeff_killCompl p x`.

Rewrite using `[this]`. Conclude with `WithPiTopology.continuous_coeff R _`.
-/
theorem continuous_killCompl [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _

/- English proof (translation)
Set `_ : UniformSpace R` to `⊥`. Establish `_ : DiscreteUniformity R` using `⟨rfl⟩`. Establish `hb` using `hasSubst_killCompl e ha`. Rewrite using `[comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]`.
-/
theorem killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]

/- English proof (translation)
Use `killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f` as an intermediate fact. Rewrite `this` using `[subst_self]`. Conclude with `this`.
-/
theorem killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  have := killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f
  rw [subst_self] at this
  exact this

end PI.OrbShared
