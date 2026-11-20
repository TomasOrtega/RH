import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog

noncomputable section

namespace PI.FglShared

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `h` using `constantCoeff_subst_of_zero (a := ex) hex0 l`. Rewrite `h` using `[hinv]`. Rewrite using `[← h]`. Conclude with `PowerSeries.constantCoeff_X`.
-/
theorem l_constantCoeff {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h := constantCoeff_subst_of_zero (a := ex) hex0 l
  rw [hinv] at h
  rw [← h]
  exact PowerSeries.constantCoeff_X

/- English proof (translation)
Establish `hex : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Establish `hy' : PowerSeries.HasSubst y` using `PowerSeries.HasSubst.of_constantCoeff_zero hy`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']`.
-/
theorem subst_subst_eq {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']

/- English proof (translation)
Introduce and unpack `rfl`. Establish `hex : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Rewrite `hinv` using `[← PowerSeries.coe_substAlgHom hex, map_zero]`. Conclude with `PowerSeries.X_ne_zero hinv.symm`.
-/
theorem l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : l ≠ 0 := by
  rintro rfl
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  rw [← PowerSeries.coe_substAlgHom hex, map_zero] at hinv
  exact PowerSeries.X_ne_zero hinv.symm

/- English proof (translation)
Establish `hl0` using `l_constantCoeff hex0 hinv`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `l_ne_zero hex0 hinv` to reduce the goal to its premises. Use extensionality with `k`.

Break down `eq_or_ne k 0 with rfl | hk` into its components or cases. Simplify using `using hl0`. Simplify using `using hc k hk`.
-/
theorem exists_coeff_ne {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : ∃ k, k ≠ 0 ∧ PowerSeries.coeff k l ≠ 0 := by
  have hl0 := l_constantCoeff hex0 hinv
  by_contra hc
  push Not at hc
  apply l_ne_zero hex0 hinv
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hl0
  · simpa using hc k hk

/- English proof (translation)
Introduce `h0`. Establish `h` using `subst_subst_eq hex0 hinv hy`. Rewrite `h` using `[h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)]`. Conclude with `hne h.symm`.
-/
theorem subst_ne_zero {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) (hne : y ≠ 0) : PowerSeries.subst y ex ≠ 0 := by
  intro h0
  have h := subst_subst_eq hex0 hinv hy
  rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)] at h
  exact hne h.symm

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst_single]`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Establish `hne : Finsupp.single i k ≠ Finsupp.single j ((Finsupp.single i k) j)`.

Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hji), Finsupp.single_zero]`. Conclude with `Finsupp.single_ne_zero.mpr hk`. Rewrite using `[if_neg hne, if_neg hji]`.
-/
theorem coeff_single_lg {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) {k : ℕ}
    (hk : k ≠ 0) : coeff (Finsupp.single i k) (PowerSeries.subst (X j : MvPowerSeries σ ℂ_[p]) l) =
      if j = i then PowerSeries.coeff k l else 0 := by
  rw [PowerSeries.coeff_subst_single]
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : Finsupp.single i k ≠ Finsupp.single j ((Finsupp.single i k) j) := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hji), Finsupp.single_zero]
      exact Finsupp.single_ne_zero.mpr hk
    rw [if_neg hne, if_neg hji]

end PI.FglShared

end
