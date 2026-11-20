import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit

noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

namespace R

variable {K : Type*} [CommRing K]

/- English proof (translation)
Establish `h1` using `PowerSeries.constantCoeff_subst (R := K) (PowerSeries.HasSubst.of_constantCoeff_zero' hex) l`. Rewrite `h1` using `[hl]`. Establish `hex' : MvPowerSeries.constantCoeff ex = 0` using `hex`. Rewrite `h1` using `[finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])]`. Simplify using `only [pow_zero, map_one, smul_eq_mul, mul_one] at h1`.

Establish `h2 : PowerSeries.coeff 0 l = 0`. Rewrite using `[← h1]`. Conclude with `PowerSeries.constantCoeff_X`. Simplify using `using h2`.
-/
theorem cc_l {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := PowerSeries.constantCoeff_subst (R := K) (PowerSeries.HasSubst.of_constantCoeff_zero' hex) l
  rw [hl] at h1
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
  simp only [pow_zero, map_one, smul_eq_mul, mul_one] at h1
  have h2 : PowerSeries.coeff 0 l = 0 := by
    rw [← h1]
    exact PowerSeries.constantCoeff_X
  simpa using h2

/- English proof (translation)
Establish `ha : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex`. Establish `hb : PowerSeries.HasSubst x` using `PowerSeries.HasSubst.of_constantCoeff_zero hx`. Rewrite using `[← PowerSeries.subst_comp_subst_apply ha hb, hl, PowerSeries.subst_X hb]`.
-/
theorem l_ex {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) {τ : Type*} {x : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x ex) l = x := by
  have ha : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hb : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← PowerSeries.subst_comp_subst_apply ha hb, hl, PowerSeries.subst_X hb]

/- English proof (translation)
The claim follows from `(PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex) (PowerSeries.HasSubst.of_constantCoeff_zero hs) ph).symm`.
-/
theorem ph_ex {ex ph : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0) {τ : Type*}
    {s : MvPowerSeries τ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    PowerSeries.subst (PowerSeries.subst s ex) ph =
      PowerSeries.subst s (PowerSeries.subst ex ph : PowerSeries K) := (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
    (PowerSeries.HasSubst.of_constantCoeff_zero hs) ph).symm

/- English proof (translation)
Rewrite using `[map_add, PowerSeries.constantCoeff_subst_eq_zero ha l hl0, PowerSeries.constantCoeff_subst_eq_zero hb l hl0, add_zero]`.
-/
theorem cc_sum {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0) {τ : Type*}
    {a b : MvPowerSeries τ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l + PowerSeries.subst b l) = 0 := by
  rw [map_add, PowerSeries.constantCoeff_subst_eq_zero ha l hl0,
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0, add_zero]

end R

section
variable {p : ℕ} [Fact p.Prime] {σ : Type*} {l ex ph : PowerSeries ℂ_[p]}

/- English proof (translation)
Unfold `PI.JetsPhW.phAt PI.JetsPhW.add psi`. Conclude with `PI.JetsPhW.W.R.ph_ex hex (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)`.
-/
theorem phAt_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph) := by
  unfold PI.JetsPhW.phAt PI.JetsPhW.add psi
  exact PI.JetsPhW.W.R.ph_ex hex
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

/- English proof (translation)
Unfold `PI.JetsPhW.add`. Conclude with `PI.JetsPhW.W.R.l_ex hex hl (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)`.
-/
theorem l_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold PI.JetsPhW.add
  exact PI.JetsPhW.W.R.l_ex hex hl
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

/- English proof (translation)
Unfold `PI.JetsPhW.add`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb) ex hex`.
-/
theorem cc_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold PI.JetsPhW.add
  exact PowerSeries.constantCoeff_subst_eq_zero
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb) ex hex

end

/- English proof (translation)
Introduce `p _ l ex ph h`. Take `⟨hex, hl, -⟩` from `h`. Establish `h0 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0` using `MvPowerSeries.constantCoeff_X _`. Establish `h1 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0` using `MvPowerSeries.constantCoeff_X _`. Establish `h2 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0` using `MvPowerSeries.constantCoeff_X _`.

Unfold `PI.JetsPhW.cubeE`. Rewrite using `[phAt_add hex hl (cc_add hex hl h0 h1) h2, l_add hex hl h0 h1, phAt_add hex hl h0 h1, phAt_add hex hl h1 h2, phAt_add hex hl h2 h0]`.
-/
theorem cubeDefectFormula_holds : Rw3 := by
  intro p _ l ex ph h
  obtain ⟨hex, hl, -⟩ := h
  have h0 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h1 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h2 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  unfold PI.JetsPhW.cubeE
  rw [phAt_add hex hl (cc_add hex hl h0 h1) h2,
    l_add hex hl h0 h1, phAt_add hex hl h0 h1,
    phAt_add hex hl h1 h2, phAt_add hex hl h2 h0]

end PI.JetsPhW.W
