import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

/- English proof (translation)
Introduce `K _ S l ex hex hl c hG σ a ha`. Take `⟨haS, ha0⟩` from `ha`. Establish `hex' : MvPowerSeries.constantCoeff ex = 0` using `hex`. Establish `hsub : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero hex'`. Establish `hl0 : PowerSeries.constantCoeff l = 0`.

Establish `h1` using `congrArg MvPowerSeries.constantCoeff hl`. Rewrite `h1` using `[PowerSeries.constantCoeff_subst hsub, finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])]`. Simplify using `using h1.trans (PowerSeries.constantCoeff_X (R := K))`. Establish `hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0` using `by simp`. Establish `hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K)` using `PowerSeries.HasSubst.of_constantCoeff_zero hX0`.

Establish `has : PowerSeries.HasSubst a` using `PowerSeries.HasSubst.of_constantCoeff_zero ha0`. Establish `hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0`. Rewrite using `[map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]`. Establish `hAs` using `PowerSeries.HasSubst.of_constantCoeff_zero hA0`. Establish `hinner : PowerSeries.subst a (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = MvPowerSeries.C c * PowerSeries.subst a l`.

Rewrite using `[← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_comp_subst_apply hXs has]`. Use `congr 1`. Establish `h2` using `(PowerSeries.substAlgHom has).commutes c`. Rewrite `h2` using `[PowerSeries.coe_substAlgHom]`. Use `first`.

Consider the case `exact h2`. Consider the case `simp`. Consider the case `(simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2`. Conclude with `h2)`. Use `congr 1`.

Conclude with `PowerSeries.subst_X has`. Establish `key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex = PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex)`. Rewrite using `[PowerSeries.subst_comp_subst_apply hAs has, hinner]`. Rewrite using `[key]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[serOver_iff]`. Conclude with `subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero ha0 _ (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)`.
-/
theorem mulGen_thm : PI.FglPtW.MulGen := by
  intro K _ S l ex hex hl c hG σ a ha
  obtain ⟨haS, ha0⟩ := ha
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero hex'

  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h1 := congrArg MvPowerSeries.constantCoeff hl
    rw [PowerSeries.constantCoeff_subst hsub,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
    simpa using h1.trans (PowerSeries.constantCoeff_X (R := K))
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0 := by simp
  have hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX0
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  have hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]
  have hAs := PowerSeries.HasSubst.of_constantCoeff_zero hA0

  have hinner : PowerSeries.subst a (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) =
      MvPowerSeries.C c * PowerSeries.subst a l := by
    rw [← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hXs has]
    congr 1
    · have h2 := (PowerSeries.substAlgHom has).commutes c
      rw [PowerSeries.coe_substAlgHom] at h2
      first
        | exact h2
        | simp
        | (simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
           exact h2)
    · congr 1
      exact PowerSeries.subst_X has
  have key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex =
      PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c *
        PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) := by
    rw [PowerSeries.subst_comp_subst_apply hAs has, hinner]
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [serOver_iff]
    exact subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)
  · exact PowerSeries.constantCoeff_subst_eq_zero ha0 _
      (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)

end PI.FglPtW.Wk

end
