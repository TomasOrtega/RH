import Mathlib
import Formalism.PeriodIntegrals.FglGram

noncomputable section

namespace PI.UnitaryGroupMassFormula.GramIso

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem l_const (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h0 : PowerSeries.HasSubst (0 : PowerSeries ℂ_[p]) := PowerSeries.HasSubst.zero'
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' he
  have key := congrArg (PowerSeries.subst (0 : PowerSeries ℂ_[p])) hl
  rw [PowerSeries.subst_comp_subst_apply hex h0, PowerSeries.subst_zero_of_constantCoeff_zero he,
    PowerSeries.subst_X h0, PowerSeries.subst_zero_eq_C_constantCoeff] at key
  have := congrArg MvPowerSeries.constantCoeff key
  simpa using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Evaluate the numerical expressions.

A detailed English derivation is pending.
-/
theorem ex_coeff_one_ne (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 ex ≠ 0 := by
  intro h1
  have hlc := l_const l ex he hl
  have h2 : ((2 : ℕ) : ℕ∞) ≤ ex.order := by
    apply PowerSeries.nat_le_order
    intro i hi
    interval_cases i
    · simpa using he
    · exact h1
  have h3 := PowerSeries.le_order_subst_right' (φ := l) he hlc
  rw [hl, PowerSeries.order_X] at h3
  have h4 := h2.trans h3
  norm_num at h4

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.
-/
theorem ex_comp_l (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hu : IsUnit (PowerSeries.coeff 1 ex) := isUnit_iff_ne_zero.mpr (ex_coeff_one_ne l ex he hl)
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' he
  have hgS : PowerSeries.HasSubst (ex.substInvOfIsUnit hu) := PowerSeries.HasSubst.substInvOfIsUnit ex hu
  have hright : PowerSeries.subst (ex.substInvOfIsUnit hu) ex = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right ex he hu
  have hg : l = ex.substInvOfIsUnit hu := by
    calc l = PowerSeries.subst PowerSeries.X l := (PowerSeries.X_subst l).symm
      _ = PowerSeries.subst (PowerSeries.subst (ex.substInvOfIsUnit hu) ex) l := by rw [hright]
      _ = PowerSeries.subst (ex.substInvOfIsUnit hu) (PowerSeries.subst ex l) :=
          (PowerSeries.subst_comp_subst_apply hex hgS l).symm
      _ = PowerSeries.subst (ex.substInvOfIsUnit hu) PowerSeries.X := by rw [hl]
      _ = ex.substInvOfIsUnit hu := PowerSeries.subst_X hgS
  rw [hg, hright]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem be_zero_left (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {r : ℕ} (j j' : Fin r) :
    be l ex ph (mulBy l ex 0 (Xv j)) (Xv j' : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
  obtain ⟨he, hl, hph⟩ := hD
  have hlc := l_const l ex he hl
  have hinv := ex_comp_l l ex he hl
  simp only [be, mulBy, add, pt, lg, phAt, map_zero, zero_mul]
  rw [PowerSeries.subst_zero_of_constantCoeff_zero he, PowerSeries.subst_zero_of_constantCoeff_zero hlc,
    zero_add, PowerSeries.subst_zero_of_constantCoeff_zero hph, sub_zero,
    ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlc)
      (PowerSeries.HasSubst.X j'), hinv, PowerSeries.subst_X (PowerSeries.HasSubst.X j')]
  exact sub_self _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem gramIso : PI.FglGram.GramIso := by
  intro p _ l ex ph hD κ _ r b hb
  simp only [GramRhs, hb, Prod.fst_zero, map_zero, zero_mul, Finset.sum_const_zero, zero_add,
    be_zero_left l ex ph hD]

end PI.UnitaryGroupMassFormula.GramIso
