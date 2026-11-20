import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLog
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffPowEqZeroOfDegreeLt

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

/- English proof (translation)
Introduce `_ _ _ i g` and use `Ch.pderiv_subst_X_self i g`.
-/
theorem pderiv_subst_self : PdSelf := fun _ _ _ i g => Ch.pderiv_subst_X_self i g

/- English proof (translation)
Introduce `_ _ _ _ _ g h` and use `Ch.pderiv_subst_X_ne h g`.
-/
theorem pderiv_subst_ne : PdNe := fun _ _ _ _ _ g h => Ch.pderiv_subst_X_ne h g

/- English proof (translation)
Introduce `p _ σ i l v g s c hv hs hpd`. Unfold `Dv`. Rewrite using `[Ch.pderiv_subst i hs, hpd]`. Take the linear combination `(MvPowerSeries.C c * PowerSeries.subst s (dX g)) * Ch.subst_v_mul hv i`.
-/
theorem derivative_chain_rule : DChain := by
  intro p _ σ i l v g s c hv hs hpd
  unfold Dv
  rw [Ch.pderiv_subst i hs, hpd]
  linear_combination (MvPowerSeries.C c * PowerSeries.subst s (dX g)) * Ch.subst_v_mul hv i

/- English proof (translation)
Introduce `p _ σ i v g`. Unfold `Dv`. Rewrite using `[Ch.pderiv_subst_X_self, ← PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) v (dX g)]`.
-/
theorem derivative_self : DSelf := by
  intro p _ σ i v g
  unfold Dv
  rw [Ch.pderiv_subst_X_self, ← PowerSeries.subst_mul
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) v (dX g)]

/- English proof (translation)
Introduce `p _ σ s g hs`. Establish `hsub : PowerSeries.HasSubst s` using `PowerSeries.HasSubst.of_constantCoeff_zero hs`. Establish `h2 : MvPowerSeries.constantCoeff (PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g))) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hs _ (by simp)`. Establish `h4 : PowerSeries.subst s g = PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g)) + MvPowerSeries.C (PowerSeries.constantCoeff g)`. Rewrite using `[← PowerSeries.subst_C (a := s) (PowerSeries.constantCoeff g), ← PowerSeries.subst_add hsub, sub_add_cancel]`.

Rewrite using `[h4, map_add, h2, zero_add, MvPowerSeries.constantCoeff_C]`.
-/
theorem evaluation_at_zero : Ev0 := by
  intro p _ σ s g hs
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have h2 : MvPowerSeries.constantCoeff
      (PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ (by simp)
  have h4 : PowerSeries.subst s g = PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g)) +
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
    rw [← PowerSeries.subst_C (a := s) (PowerSeries.constantCoeff g), ← PowerSeries.subst_add hsub,
      sub_add_cancel]
  rw [h4, map_add, h2, zero_add, MvPowerSeries.constantCoeff_C]

/- English proof (translation)
Introduce `p _ ex ph n`. Establish `h : (dX (A` using `ℂ_[p])) = ⇑(PowerSeries.derivative ℂ_[p]) := funext Ch.dX_eq`. Rewrite using `[h, PowerSeries.constantCoeff_iterate_derivative]`. Both sides reduce to the same expression.
-/
theorem jet_derivative_integrality : JetD := by
  intro p _ ex ph n
  have h : (dX (A := ℂ_[p])) = ⇑(PowerSeries.derivative ℂ_[p]) := funext Ch.dX_eq
  rw [h, PowerSeries.constantCoeff_iterate_derivative]
  rfl

/- English proof (translation)
Introduce `e`. Rewrite using `[PowerSeries.coeff_subst_single]`. Use `split_ifs`. Conclude with `hv _`. Use `show ‖(0 : ℂ_[p])‖ ≤ 1`.

Simplify using the standard rewrite rules.
-/
theorem intMv_subst_X {p : ℕ} [Fact p.Prime] {σ : Type*} {v : PowerSeries ℂ_[p]} (hv : IntP v) (i : σ) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hv _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

/- English proof (translation)
Introduce `_ _ _ i _ _ hv hf` and use `intMv_mul (intMv_subst_X hv i) (intMv_pderiv i hf)`.
-/
theorem derivative_integral : Dint := fun _ _ _ i _ _ hv hf => intMv_mul (intMv_subst_X hv i) (intMv_pderiv i hf)

/- English proof (translation)
Introduce `_ _ _ i _ _ hv hf hE` and use `L0 i hf hE (intMv_subst_X hv i)`.
-/
theorem log_derivative_integral_jet_integrality : LogDer := fun _ _ _ i _ _ hv hf hE => L0 i hf hE (intMv_subst_X hv i)

end PI.JetsPhW.W
