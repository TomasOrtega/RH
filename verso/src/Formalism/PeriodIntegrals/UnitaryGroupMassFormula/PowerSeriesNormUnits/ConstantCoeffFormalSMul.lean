import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section One

variable {l ex : PowerSeries ℂ_[p]}

/- English proof (translation)
Establish `h1` using `congrArg (MvPowerSeries.constantCoeff (σ := Unit) (R := ℂ_[p])) hinv`. Rewrite `h1` using `[PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hex0)]`. Rewrite `h1` using `[finsum_eq_single _ 0]`. Establish `h2 : PowerSeries.constantCoeff l = MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[p])`. Simplify using `using h1`.

Conclude with `h2.trans PowerSeries.constantCoeff_X`. Introduce `d hd`. Rewrite using `[map_pow]`. Express the relevant statement in the definitionally equal form `PowerSeries.coeff d l • (PowerSeries.constantCoeff ex) ^ d = 0`. Rewrite using `[hex0, zero_pow hd, smul_zero]`.
-/
theorem l_const (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := congrArg (MvPowerSeries.constantCoeff (σ := Unit) (R := ℂ_[p])) hinv
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hex0)] at h1
  rw [finsum_eq_single _ 0] at h1
  · have h2 : PowerSeries.constantCoeff l =
        MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[p]) := by
      simpa using h1
    exact h2.trans PowerSeries.constantCoeff_X
  · intro d hd
    rw [map_pow]
    change PowerSeries.coeff d l • (PowerSeries.constantCoeff ex) ^ d = 0
    rw [hex0, zero_pow hd, smul_zero]

/- English proof (translation)
Introduce `h1`. Establish `hl0` using `l_const hex0 hinv`. Establish `hX2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ l`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`.

Use `interval_cases m`. Simplify using `using hl0`. Conclude with `h1`. Take `⟨q, hq⟩` from `hX2`. Take `⟨e', he'⟩` from `PowerSeries.X_dvd_iff.mpr hex0`.

Establish `hs : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Establish `key : PowerSeries.subst ex l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * (e' ^ 2 * PowerSeries.subst ex q)`. Rewrite using `[hq, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, he']`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hinv]`.

Establish `h2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ PowerSeries.X` using `⟨_, key⟩`. Rewrite `h2` using `[PowerSeries.X_pow_dvd_iff]`. Simplify using `using h2 1 (by norm_num)`.
-/
theorem coeff_one_l_ne (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hl0 := l_const hex0 hinv
  have hX2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ l := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa using hl0
    · exact h1
  obtain ⟨q, hq⟩ := hX2
  obtain ⟨e', he'⟩ := PowerSeries.X_dvd_iff.mpr hex0
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 *
      (e' ^ 2 * PowerSeries.subst ex q) := by
    rw [hq, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, he']
    ring
  rw [hinv] at key
  have h2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ PowerSeries.X := ⟨_, key⟩
  rw [PowerSeries.X_pow_dvd_iff] at h2
  simpa using h2 1 (by norm_num)

/- English proof (translation)
Establish `hl0` using `l_const hex0 hinv`. Establish `hu : IsUnit (PowerSeries.coeff 1 l)` using `isUnit_iff_ne_zero.mpr (coeff_one_l_ne hex0 hinv)`. Use `set Q := PowerSeries.substInvOfIsUnit l hu`. Establish `hQl : PowerSeries.subst l Q = PowerSeries.X` using `PowerSeries.subst_substInvOfIsUnit_left l hl0 hu`. Establish `hexQ : ex = Q`.

Establish `hs : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Establish `hsl : PowerSeries.HasSubst l` using `PowerSeries.HasSubst.of_constantCoeff_zero' hl0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hexQ]`. Conclude with `hQl`.
-/
theorem ex_l (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hl0 := l_const hex0 hinv
  have hu : IsUnit (PowerSeries.coeff 1 l) := isUnit_iff_ne_zero.mpr (coeff_one_l_ne hex0 hinv)
  set Q := PowerSeries.substInvOfIsUnit l hu
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hexQ : ex = Q := by
    have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    have hsl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
    calc ex = PowerSeries.subst ex (PowerSeries.X : PowerSeries ℂ_[p]) := (PowerSeries.subst_X hs).symm
      _ = PowerSeries.subst ex (PowerSeries.subst l Q) := by rw [hQl]
      _ = PowerSeries.subst (PowerSeries.subst ex l) Q := PowerSeries.subst_comp_subst_apply hsl hs Q
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) Q := by rw [hinv]
      _ = Q := PowerSeries.X_subst Q
  rw [hexQ]; exact hQl

end One

section Law

variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
variable {τ : Type*}

include hex0 hinv

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst ex` using `PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Establish `hb' : PowerSeries.HasSubst b` using `PowerSeries.HasSubst.of_constantCoeff_zero hb`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hs hb', hinv, PowerSeries.subst_X hb']`.
-/
theorem L_E (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (PowerSeries.subst b ex) l = b := by
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hb' : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  rw [← PowerSeries.subst_comp_subst_apply hs hb', hinv, PowerSeries.subst_X hb']

/- English proof (translation)
Establish `hl0` using `l_const hex0 hinv`. Establish `hs : PowerSeries.HasSubst l` using `PowerSeries.HasSubst.of_constantCoeff_zero' hl0`. Establish `ha' : PowerSeries.HasSubst a` using `PowerSeries.HasSubst.of_constantCoeff_zero ha`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hs ha', ex_l hex0 hinv, PowerSeries.subst_X ha']`.
-/
theorem E_L (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a l) ex = a := by
  have hl0 := l_const hex0 hinv
  have hs : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.subst_comp_subst_apply hs ha', ex_l hex0 hinv, PowerSeries.subst_X ha']

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero ha l (l_const hex0 hinv)`.
-/
theorem constantCoeff_subst_log (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha l (l_const hex0 hinv)

omit hinv in
/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero hb ex hex0`.
-/
theorem z0_pt_zero_pt_one_L3 (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst b ex) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hb ex hex0

/- English proof (translation)
Unfold `add`. Apply `z0_pt_zero_pt_one_L3 hex0` to reduce the goal to its premises. Rewrite using `[map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]`.
-/
theorem constantCoeff_formalAdd (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold add
  apply z0_pt_zero_pt_one_L3 hex0
  rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]

/- English proof (translation)
Unfold `mulBy`. Apply `z0_pt_zero_pt_one_L3 hex0` to reduce the goal to its premises. Rewrite using `[map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]`.
-/
theorem constantCoeff_formalSMul (c : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 := by
  unfold mulBy
  apply z0_pt_zero_pt_one_L3 hex0
  rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]

/- English proof (translation)
Unfold `add`. Apply `L_E hex0 hinv` to reduce the goal to its premises. Rewrite using `[map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]`.
-/
theorem L_add (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold add
  apply L_E hex0 hinv
  rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]

/- English proof (translation)
Unfold `mulBy`. Apply `L_E hex0 hinv` to reduce the goal to its premises. Rewrite using `[map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]`.
-/
theorem L_mulBy (c : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (mulBy l ex c a) l = MvPowerSeries.C c * PowerSeries.subst a l := by
  unfold mulBy
  apply L_E hex0 hinv
  rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]

/- English proof (translation)
Use `show PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst (mulBy l ex d a) l) ex = _`. Rewrite using `[L_mulBy hex0 hinv d a ha, ← mul_assoc, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem mulBy_mulBy (c d : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex c (mulBy l ex d a) = mulBy l ex (c * d) a := by
  show PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst (mulBy l ex d a) l) ex = _
  rw [L_mulBy hex0 hinv d a ha, ← mul_assoc, ← map_mul]
  rfl

/- English proof (translation)
Unfold `add`. Rewrite using `[L_mulBy hex0 hinv c a ha, L_mulBy hex0 hinv d a ha, ← add_mul, ← map_add]`. Both sides reduce to the same expression.
-/
theorem add_mulBy (c d : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a := by
  unfold add
  rw [L_mulBy hex0 hinv c a ha, L_mulBy hex0 hinv d a ha, ← add_mul, ← map_add]
  rfl

/- English proof (translation)
Unfold `mulBy`. Rewrite using `[L_add hex0 hinv a b ha hb]`. Unfold `add`. Rewrite using `[L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]), L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv b hb, mul_zero]), mul_add]`.
-/
theorem mulBy_add (c : ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    mulBy l ex c (add l ex a b) = add l ex (mulBy l ex c a) (mulBy l ex c b) := by
  unfold mulBy
  rw [L_add hex0 hinv a b ha hb]
  unfold add
  rw [L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]),
    L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv b hb, mul_zero]), mul_add]

omit hex0 hinv in
/- English proof (translation)
Unfold `add`. Rewrite using `[add_comm]`.
-/
theorem add_comm' (a b : MvPowerSeries τ ℂ_[p]) : add l ex a b = add l ex b a := by
  unfold add; rw [add_comm]

/- English proof (translation)
Unfold `mulBy`. Rewrite using `[map_one, one_mul]`. Conclude with `E_L hex0 hinv a ha`.
-/
theorem mulBy_one (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex 1 a = a := by
  unfold mulBy; rw [map_one, one_mul]; exact E_L hex0 hinv a ha

omit hinv in
/- English proof (translation)
Unfold `mulBy`. Rewrite using `[map_zero, zero_mul, PowerSeries.subst_zero_of_constantCoeff_zero hex0]`.
-/
theorem mulBy_zero' (a : MvPowerSeries τ ℂ_[p]) : mulBy l ex 0 a = 0 := by
  unfold mulBy
  rw [map_zero, zero_mul, PowerSeries.subst_zero_of_constantCoeff_zero hex0]

/- English proof (translation)
Rewrite using `[show (2 : ℂ_[p]) = 1 + 1 by norm_num, ← add_mulBy hex0 hinv 1 1 a ha, mulBy_one hex0 hinv a ha]`.
-/
theorem add_self (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex a a = mulBy l ex 2 a := by
  rw [show (2 : ℂ_[p]) = 1 + 1 by norm_num, ← add_mulBy hex0 hinv 1 1 a ha, mulBy_one hex0 hinv a ha]

/- English proof (translation)
Rewrite using `[show ((k + 1 : ℕ) : ℂ_[p]) = (k : ℂ_[p]) + 1 by push_cast; ring, ← add_mulBy hex0 hinv _ _ a ha, mulBy_one hex0 hinv a ha]`.
-/
theorem mulBy_succ (k : ℕ) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex ((k + 1 : ℕ) : ℂ_[p]) a = add l ex (mulBy l ex (k : ℂ_[p]) a) a := by
  rw [show ((k + 1 : ℕ) : ℂ_[p]) = (k : ℂ_[p]) + 1 by push_cast; ring, ← add_mulBy hex0 hinv _ _ a ha,
    mulBy_one hex0 hinv a ha]

omit hex0 hinv in
/- English proof (translation)
Unfold `be`. Rewrite using `[add_comm' a b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem be_comm (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) :
    be l ex ph a b = be l ex ph b a := by
  unfold be; rw [add_comm' a b]; ring

end Law

section Subst

variable {σ τ : Type*} [Finite σ] {l ex : PowerSeries ℂ_[p]} (s : σ → MvPowerSeries τ ℂ_[p])
  (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)

include hs

/- English proof (translation)
Establish `hS : MvPowerSeries.HasSubst s` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hs`. Establish `ha' : MvPowerSeries.HasSubst (fun _ : Unit => a)` using `(PowerSeries.HasSubst.of_constantCoeff_zero ha).const`. Rewrite using `[PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha' hS]`. Both sides reduce to the same expression.
-/
theorem sb_psubst (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha' hS]
  rfl

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) i`.
-/
theorem sb_X (i : σ) : MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i :=
  MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) i

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G`.
-/
theorem sb_add' (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F + G) = MvPowerSeries.subst s F + MvPowerSeries.subst s G :=
  MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G`.
-/
theorem sb_sub' (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F - G) = MvPowerSeries.subst s F - MvPowerSeries.subst s G :=
  MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero hs), MvPowerSeries.subst_C]`.
-/
theorem sb_C_mul (c : ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (MvPowerSeries.C c * F) = MvPowerSeries.C c * MvPowerSeries.subst s F := by
  rw [MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero hs), MvPowerSeries.subst_C]

variable (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv

/- English proof (translation)
Unfold `add`. Rewrite using `[sb_psubst s hs _ (by rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]), sb_add' s hs, sb_psubst s hs a ha, sb_psubst s hs b hb]`.
-/
theorem sb_add (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold add
  rw [sb_psubst s hs _ (by rw [map_add, constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]),
    sb_add' s hs, sb_psubst s hs a ha, sb_psubst s hs b hb]

/- English proof (translation)
Unfold `mulBy`. Rewrite using `[sb_psubst s hs _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]), sb_C_mul s hs, sb_psubst s hs a ha]`.
-/
theorem sb_mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a) := by
  unfold mulBy
  rw [sb_psubst s hs _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]), sb_C_mul s hs,
    sb_psubst s hs a ha]

omit hex0 hinv in
/- English proof (translation)
The claim follows from `sb_psubst s hs a ha ph`.
-/
theorem sb_phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) :=
  sb_psubst s hs a ha ph

/- English proof (translation)
Unfold `be`. Rewrite using `[sb_sub' s hs, sb_sub' s hs, sb_phAt s hs ph _ (constantCoeff_formalAdd hex0 hinv a b ha hb), sb_add s hs hex0 hinv a b ha hb, sb_phAt s hs ph a ha, sb_phAt s hs ph b hb]`.
-/
theorem sb_be (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) =
      be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold be
  rw [sb_sub' s hs, sb_sub' s hs, sb_phAt s hs ph _ (constantCoeff_formalAdd hex0 hinv a b ha hb), sb_add s hs hex0 hinv a b ha hb,
    sb_phAt s hs ph a ha, sb_phAt s hs ph b hb]

end Subst

end PI.PhNormUnits.UnitaryGroupMassFormula
