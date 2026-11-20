import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

/- English proof (translation)
Introduce `K _ S l ex hex0 hinv hF σ a b ha hb`. Establish `hcc : ∀ {τ : Type} (f : PowerSeries K) (c : MvPowerSeries τ K), MvPowerSeries.constantCoeff c = 0 → MvPowerSeries.constantCoeff (PowerSeries.subst c f) = PowerSeries.constantCoeff f`. Introduce `τ f c hc`. Rewrite using `[PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]`. Rewrite using `[finsum_eq_single _ 0]`.

Simplify using the standard rewrite rules. Introduce `d hd`. Rewrite using `[map_pow, hc, zero_pow hd, smul_zero]`. Establish `hl0 : PowerSeries.constantCoeff l = 0`. Establish `h` using `hcc l ex hex0`.

Rewrite `h` using `[hinv]`. Rewrite using `[← h]`. Conclude with `PowerSeries.constantCoeff_X`. Establish `hP0 : ∀ s, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ K) s) = 0`. Introduce `s`.

Apply the tactic sequence `fin_cases s <;> simp [ha.2, hb.2]`. Establish `hP : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ K)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hP0`. Establish `hmix : ∀ (c : MvPowerSeries (Fin 2) K), MvPowerSeries.constantCoeff c = 0 → ∀ f : PowerSeries K, MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst c f) = PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) c) f`. Introduce `c hc f`. Conclude with `MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hc)) hP f`.

Establish `hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `MvPowerSeries.constantCoeff_X 0`. Establish `hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `MvPowerSeries.constantCoeff_X 1`. Establish `hG0 : MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = 0`. Rewrite using `[map_add, hcc l _ hX0, hcc l _ hX1, hl0, add_zero]`. Establish `hG : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = PowerSeries.subst a l + PowerSeries.subst b l`.

Rewrite using `[MvPowerSeries.subst_add hP, hmix _ hX0, hmix _ hX1, MvPowerSeries.subst_X hP, MvPowerSeries.subst_X hP]`. Both sides reduce to the same expression. Establish `heq : PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex = MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin …`. Rewrite using `[hmix _ hG0, hG]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[heq, serOver_iff]`. Use `mvsubst_mem_SerS S hP0 (fun i => ?_) ((serOver_iff S _).mp hF)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> simp [(serOver_iff S a).mp ha.1, (serOver_iff S b).mp hb.1]`. Rewrite using `[hcc ex _ (by rw [map_add, hcc l a ha.2, hcc l b hb.2, hl0, add_zero])]`. Conclude with `hex0`.
-/
theorem addGen_thm : PI.FglPtW.AddGen := by
  intro K _ S l ex hex0 hinv hF σ a b ha hb
  have hcc : ∀ {τ : Type} (f : PowerSeries K) (c : MvPowerSeries τ K),
      MvPowerSeries.constantCoeff c = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst c f) = PowerSeries.constantCoeff f := by
    intro τ f c hc
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [map_pow, hc, zero_pow hd, smul_zero]
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := hcc l ex hex0
    rw [hinv] at h
    rw [← h]
    exact PowerSeries.constantCoeff_X
  have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ K) s) = 0 := by
    intro s
    fin_cases s <;> simp [ha.2, hb.2]
  have hP : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  have hmix : ∀ (c : MvPowerSeries (Fin 2) K), MvPowerSeries.constantCoeff c = 0 →
      ∀ f : PowerSeries K, MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst c f) =
        PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) c) f := by
    intro c hc f
    exact MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hc)) hP f
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hG0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add, hcc l _ hX0, hcc l _ hX1, hl0, add_zero]
  have hG : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) =
      PowerSeries.subst a l + PowerSeries.subst b l := by
    rw [MvPowerSeries.subst_add hP, hmix _ hX0, hmix _ hX1, MvPowerSeries.subst_X hP,
      MvPowerSeries.subst_X hP]
    rfl
  have heq : PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
      MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) := by
    rw [hmix _ hG0, hG]
  refine ⟨?_, ?_⟩
  · rw [heq, serOver_iff]
    refine mvsubst_mem_SerS S hP0 (fun i => ?_) ((serOver_iff S _).mp hF)
    fin_cases i <;> simp [(serOver_iff S a).mp ha.1, (serOver_iff S b).mp hb.1]
  · rw [hcc ex _ (by rw [map_add, hcc l a ha.2, hcc l b hb.2, hl0, add_zero])]
    exact hex0

end PI.FglPtW.Wk

end
