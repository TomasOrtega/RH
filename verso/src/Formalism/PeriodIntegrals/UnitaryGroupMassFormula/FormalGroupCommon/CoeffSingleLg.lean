import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog

noncomputable section

namespace PI.FglShared

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem l_constantCoeff {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h := constantCoeff_subst_of_zero (a := ex) hex0 l
  rw [hinv] at h
  rw [← h]
  exact PowerSeries.constantCoeff_X

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem subst_subst_eq {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : l ≠ 0 := by
  rintro rfl
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  rw [← PowerSeries.coe_substAlgHom hex, map_zero] at hinv
  exact PowerSeries.X_ne_zero hinv.symm

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem subst_ne_zero {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) (hne : y ≠ 0) : PowerSeries.subst y ex ≠ 0 := by
  intro h0
  have h := subst_subst_eq hex0 hinv hy
  rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)] at h
  exact hne h.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
