import Mathlib
import Formalism.PeriodIntegrals.JetsPhW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLow

noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

/- English proof (translation)
Take `⟨hex, hsub, v, hvint, hv⟩` from `h`. Establish `hl0 : PowerSeries.constantCoeff l = 0`. Establish `hc` using `congrArg MvPowerSeries.constantCoeff hsub`. Rewrite `hc` using `[const_subst hex]`. Rewrite using `[hc]`.

Conclude with `PowerSeries.constantCoeff_X`. Establish `hl1 : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1`. Establish `hc` using `congrArg (PowerSeries.coeff 1) hsub`. Rewrite `hc` using `[pcoeff1_subst hex l, PowerSeries.coeff_one_X]`. Conclude with `hc`.

Establish `hv0 : PowerSeries.coeff 0 v * PowerSeries.coeff 1 l = 1`. Establish `hc` using `congrArg (PowerSeries.coeff 0) hv`. Simplify `hc` using `[PowerSeries.coeff_mul, dX]`. Establish `hev : PowerSeries.coeff 1 ex = PowerSeries.coeff 0 v`. Take the linear combination `PowerSeries.coeff 0 v * hl1 - PowerSeries.coeff 1 ex * hv0`.

Use `⟨hl0, hl1, ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`. Conclude with `hvint 0`.
-/
theorem logOk_low {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (h : LogOk l ex) :
    PowerSeries.constantCoeff l = 0 ∧
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 ∧ ‖PowerSeries.coeff 1 ex‖ ≤ 1 := by
  obtain ⟨hex, hsub, v, hvint, hv⟩ := h
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hc := congrArg MvPowerSeries.constantCoeff hsub
    rw [const_subst hex] at hc
    rw [hc]
    exact PowerSeries.constantCoeff_X
  have hl1 : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hsub
    rw [pcoeff1_subst hex l, PowerSeries.coeff_one_X] at hc
    exact hc
  have hv0 : PowerSeries.coeff 0 v * PowerSeries.coeff 1 l = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hv
    simpa [PowerSeries.coeff_mul, dX] using hc
  have hev : PowerSeries.coeff 1 ex = PowerSeries.coeff 0 v := by
    linear_combination PowerSeries.coeff 0 v * hl1 - PowerSeries.coeff 1 ex * hv0
  refine ⟨hl0, hl1, ?_⟩
  rw [hev]
  exact hvint 0

/- English proof (translation)
Introduce `p _ l ex ph h hp hs`. Take `⟨_, _, h2⟩` from `logOk_low h`. Establish `h1` using `(logOk_low h).2.1`. Establish `h0` using `(logOk_low h).1`. Establish `hex` using `h.1`.

Establish `hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1` using `by simp`. Establish `hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0` using `by simp [Xv]`. Establish `hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1`. Simplify using `[Xv, MvPowerSeries.coeff_X]`. Establish `hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0`.

Rewrite using `[const_subst hX0]`. Conclude with `h0`. Establish `hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = PowerSeries.coeff 1 l`. Rewrite using `[coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]`. Establish `hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0`.

Rewrite using `[map_mul, hL0, mul_zero]`. Establish `hBe : MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l`. Rewrite using `[MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]`. Establish `hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0`. Rewrite using `[mulBy, const_subst hB0]`.

Conclude with `hex`. Establish `hAe : MvPowerSeries.coeff (Finsupp.single () 1) (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1`. Rewrite using `[mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]`. Take the linear combination `(-1 : ℂ_[p]) * h1`. Establish `hf : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph`.

Rewrite using `[phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]`. Establish `hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) = PowerSeries.coeff 1 ph`. Rewrite using `[phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]`. Establish `hint` using `hs.2 (Finsupp.single () 1)`. Unfold `IsIntP at hint`.

Rewrite `hint` using `[coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg]`. Establish `hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1`. Establish `h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph)`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hint` using `[h2c, norm_neg, norm_mul, norm_two hp, one_mul]`.

Conclude with `hint`. Use `show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1`. Rewrite using `[pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]`. Conclude with `mul_le_one₀ hc (norm_nonneg _) h2`.
-/
theorem firstJetIntegralGeneral_holds : OneG := by
  intro p _ l ex ph h hp hs
  obtain ⟨_, _, h2⟩ := logOk_low h
  have h1 := (logOk_low h).2.1
  have h0 := (logOk_low h).1
  have hex := h.1
  have hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1 := by simp
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp [Xv]
  have hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X]
  have hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [const_subst hX0]
    exact h0
  have hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) =
      PowerSeries.coeff 1 l := by
    rw [coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]
  have hB0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hBe : MvPowerSeries.coeff (Finsupp.single () 1)
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l := by
    rw [MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]
  have hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [mulBy, const_subst hB0]
    exact hex
  have hAe : MvPowerSeries.coeff (Finsupp.single () 1)
      (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1 := by
    rw [mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]
    linear_combination (-1 : ℂ_[p]) * h1
  have hf : MvPowerSeries.coeff (Finsupp.single () 1)
      (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]
  have hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]
  have hint := hs.2 (Finsupp.single () 1)
  unfold IsIntP at hint
  rw [coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg] at hint
  have hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1 := by
    have h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph) := by
      ring
    rw [h2c, norm_neg, norm_mul, norm_two hp, one_mul] at hint
    exact hint
  show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1
  rw [pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) h2

end PI.JetsPhW.Low
