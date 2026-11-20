import Mathlib
import Formalism.PeriodIntegrals.FglGram

noncomputable section

open PowerSeries

namespace PI.UnitaryGroupMassFormula.GramUnit

/- English proof (translation)
Establish `hex : HasSubst ex` using `HasSubst.of_constantCoeff_zero' h0`. Take `⟨u, hu⟩ : (X : PowerSeries K) ∣ ex` from `X_dvd_iff.mpr h0`. Establish `hc : constantCoeff l = 0`. Establish `h1` using `congrArg (coeff 0) hle`. Rewrite `h1` using `[coeff_subst' hex, finsum_eq_single _ 0]`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `using h1`. Introduce `d hd`. Rewrite using `[hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]`. Establish `h1 : coeff 1 l * coeff 1 ex = 1`.

Establish `h1` using `congrArg (coeff 1) hle`. Rewrite `h1` using `[coeff_subst' hex, finsum_eq_single _ 1]`. Simplify using `using h1`. Introduce `d hd`. Break down `d with _ | _ | d` into its components or cases.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hd`. Rewrite using `[hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]`. Establish `hunit : IsUnit (coeff 1 ex)` using `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)`. Take `⟨q, hq, hr⟩ : ∃ q : PowerSeries K, HasSubst q ∧ subst q ex = X` from `⟨_, HasSubst.substInvOfIsUnit ex hunit, subst_substInvOfIsUnit_right ex h0 hunit⟩`.

Establish `e1 : subst q (subst ex l) = subst (subst q ex) l` using `subst_comp_subst_apply hex hq l`. Rewrite `e1` using `[hr, hle, X_subst, subst_X hq]`. Use `⟨?_, hc⟩` and prove the remaining obligations. Rewrite using `[← e1]`. Conclude with `hr`.
-/
theorem inv_of_left {K : Type*} [Field K] (l ex : PowerSeries K) (h0 : constantCoeff ex = 0)
    (hle : subst ex l = X) : subst l ex = X ∧ constantCoeff l = 0 := by
  have hex : HasSubst ex := HasSubst.of_constantCoeff_zero' h0
  obtain ⟨u, hu⟩ : (X : PowerSeries K) ∣ ex := X_dvd_iff.mpr h0
  have hc : constantCoeff l = 0 := by
    have h1 := congrArg (coeff 0) hle
    rw [coeff_subst' hex, finsum_eq_single _ 0] at h1
    · rw [← coeff_zero_eq_constantCoeff_apply]
      simpa using h1
    · intro d hd
      rw [hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  have h1 : coeff 1 l * coeff 1 ex = 1 := by
    have h1 := congrArg (coeff 1) hle
    rw [coeff_subst' hex, finsum_eq_single _ 1] at h1
    · simpa using h1
    · intro d hd
      rcases d with _ | _ | d
      · simp
      · exact absurd rfl hd
      · rw [hu, mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]
  have hunit : IsUnit (coeff 1 ex) := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
  obtain ⟨q, hq, hr⟩ : ∃ q : PowerSeries K, HasSubst q ∧ subst q ex = X :=
    ⟨_, HasSubst.substInvOfIsUnit ex hunit, subst_substInvOfIsUnit_right ex h0 hunit⟩
  have e1 : subst q (subst ex l) = subst (subst q ex) l := subst_comp_subst_apply hex hq l
  rw [hr, hle, X_subst, subst_X hq] at e1
  refine ⟨?_, hc⟩
  rw [← e1]
  exact hr

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Take `⟨h0, hle, hph⟩` from `hD`. Establish `hl` using `inv_of_left l ex h0 hle`. Establish `hHl : HasSubst l` using `HasSubst.of_constantCoeff_zero' hl.2`. Establish `hHb : HasSubst b` using `HasSubst.of_constantCoeff_zero hb`. Establish `hs0 : PI.FglGram.mulBy l ex 0 a = 0`.

Simplify using `only [PI.FglGram.mulBy, PI.FglGram.pt, map_zero, zero_mul]`. Conclude with `subst_zero_of_constantCoeff_zero h0`. Establish `hadd : PI.FglGram.add l ex 0 b = b`. Simplify using `only [PI.FglGram.add, PI.FglGram.pt, PI.FglGram.lg]`. Rewrite using `[subst_zero_of_constantCoeff_zero hl.2, zero_add, ← subst_comp_subst_apply hHl hHb, hl.1, subst_X hHb]`.

Simplify using `only [PI.FglGram.be, hs0, hadd, PI.FglGram.phAt, subst_zero_of_constantCoeff_zero hph, sub_zero, sub_self]`.
-/
theorem be_mulBy_zero (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {σ : Type*}
    (a b : MvPowerSeries σ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph (mulBy l ex 0 a) b = 0 := by
  obtain ⟨h0, hle, hph⟩ := hD
  have hl := inv_of_left l ex h0 hle
  have hHl : HasSubst l := HasSubst.of_constantCoeff_zero' hl.2
  have hHb : HasSubst b := HasSubst.of_constantCoeff_zero hb
  have hs0 : PI.FglGram.mulBy l ex 0 a = 0 := by
    simp only [PI.FglGram.mulBy, PI.FglGram.pt, map_zero, zero_mul]
    exact subst_zero_of_constantCoeff_zero h0
  have hadd : PI.FglGram.add l ex 0 b = b := by
    simp only [PI.FglGram.add, PI.FglGram.pt, PI.FglGram.lg]
    rw [subst_zero_of_constantCoeff_zero hl.2, zero_add, ← subst_comp_subst_apply hHl hHb, hl.1,
      subst_X hHb]
  simp only [PI.FglGram.be, hs0, hadd, PI.FglGram.phAt, subst_zero_of_constantCoeff_zero hph, sub_zero,
    sub_self]

/- English proof (translation)
Introduce `p _ l ex ph hD n de hde`. Combine the equalities or inequalities in the displayed calculation. Unfold `PI.FglGram.GramRhs`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by`.

Rewrite using `[hde j j, if_pos rfl, Prod.fst_one, map_one, one_mul]`. Conclude with `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' hj' => by`. Rewrite using `[hde j j', if_neg (ne_of_lt (Finset.mem_filter.mp hj').2), Prod.fst_zero]`. Conclude with `be_mulBy_zero l ex ph hD _ _ (MvPowerSeries.constantCoeff_X _)`. Use `_ = _ := add_zero _`.
-/
theorem gramUnit : GramUnit := by
  intro p _ l ex ph hD n de hde
  calc PI.FglGram.GramRhs l ex ph de = (∑ j, PI.FglGram.phAt ph (PI.FglGram.Xv j) : MvPowerSeries (Fin n) ℂ_[p]) + 0 := by
        unfold PI.FglGram.GramRhs
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by
            rw [hde j j, if_pos rfl, Prod.fst_one, map_one, one_mul]
        · exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' hj' => by
            rw [hde j j', if_neg (ne_of_lt (Finset.mem_filter.mp hj').2), Prod.fst_zero]
            exact be_mulBy_zero l ex ph hD _ _ (MvPowerSeries.constantCoeff_X _)
    _ = _ := add_zero _

end PI.UnitaryGroupMassFormula.GramUnit
