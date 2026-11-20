import Mathlib
import Formalism.PeriodIntegrals.FglTriFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CoeffSubstUpdZero

noncomputable section

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst (fun _ : Unit => a)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)`. Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hA hb]`.
-/
theorem psubst_comm {σ τ : Type*} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  have hA : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hA hb]

section Ops

variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero ha l hl`.
-/
theorem cc_lg (hl : PowerSeries.constantCoeff l = 0) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.constantCoeff (lg l a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha l hl

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero ha ex hex`.
-/
theorem cc_pt (hex : PowerSeries.constantCoeff ex = 0) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.constantCoeff (pt ex a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha ex hex

/- English proof (translation)
Establish `h : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l a + PI.FglTriFactor.lg l b) = 0`. Rewrite using `[map_add, cc_lg hl ha, cc_lg hl hb, add_zero]`. Conclude with `cc_pt hex h`.
-/
theorem cc_add (hl : PowerSeries.constantCoeff l = 0) (hex : PowerSeries.constantCoeff ex = 0)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  have h : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l a + PI.FglTriFactor.lg l b) = 0 := by
    rw [map_add, cc_lg hl ha, cc_lg hl hb, add_zero]
  exact cc_pt hex h

/- English proof (translation)
The claim follows from `psubst_comm ha hb l`.
-/
theorem subst_lg {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (lg l a) = lg l (MvPowerSeries.subst b a) :=
  psubst_comm ha hb l

/- English proof (translation)
The claim follows from `psubst_comm ha hb ex`.
-/
theorem subst_pt {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (pt ex a) = pt ex (MvPowerSeries.subst b a) :=
  psubst_comm ha hb ex

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x + PI.FglTriFactor.lg l y) = 0`. Rewrite using `[map_add, cc_lg hl hx, cc_lg hl hy, add_zero]`. Unfold `PI.FglTriFactor.add`. Rewrite using `[subst_pt hb h0, MvPowerSeries.subst_add hb, subst_lg hb hx, subst_lg hb hy]`.
-/
theorem subst_add (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (add l ex x y) = add l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by
  have h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x + PI.FglTriFactor.lg l y) = 0 := by
    rw [map_add, cc_lg hl hx, cc_lg hl hy, add_zero]
  unfold PI.FglTriFactor.add
  rw [subst_pt hb h0, MvPowerSeries.subst_add hb, subst_lg hb hx, subst_lg hb hy]

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x - PI.FglTriFactor.lg l y) = 0`. Rewrite using `[map_sub, cc_lg hl hx, cc_lg hl hy, sub_zero]`. Unfold `PI.FglTriFactor.sub`. Rewrite using `[subst_pt hb h0, MvPowerSeries.subst_sub hb, subst_lg hb hx, subst_lg hb hy]`.
-/
theorem subst_sub (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (sub l ex x y) = sub l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by
  have h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x - PI.FglTriFactor.lg l y) = 0 := by
    rw [map_sub, cc_lg hl hx, cc_lg hl hy, sub_zero]
  unfold PI.FglTriFactor.sub
  rw [subst_pt hb h0, MvPowerSeries.subst_sub hb, subst_lg hb hx, subst_lg hb hy]

/- English proof (translation)
Establish `hY' : PowerSeries.HasSubst Y` using `PowerSeries.HasSubst.of_constantCoeff_zero hY`. Unfold `PI.FglTriFactor.lg PI.FglTriFactor.pt`. Rewrite using `[← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex0) hY', hinv, PowerSeries.subst_X hY']`.
-/
theorem lg_pt (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
    {Y : MvPowerSeries σ ℂ_[p]} (hY : MvPowerSeries.constantCoeff Y = 0) : lg l (pt ex Y) = Y := by
  have hY' : PowerSeries.HasSubst Y := PowerSeries.HasSubst.of_constantCoeff_zero hY
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex0) hY', hinv,
    PowerSeries.subst_X hY']

/- English proof (translation)
Establish `hx' : PowerSeries.HasSubst x` using `PowerSeries.HasSubst.of_constantCoeff_zero hx`. Unfold `PI.FglTriFactor.lg PI.FglTriFactor.pt`. Rewrite using `[← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hx', hinv, PowerSeries.subst_X hx']`.
-/
theorem pt_lg (hl0 : PowerSeries.constantCoeff l = 0) (hinv : PowerSeries.subst l ex = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) : pt ex (lg l x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hx', hinv,
    PowerSeries.subst_X hx']

/- English proof (translation)
The claim follows from `PowerSeries.subst_zero_of_constantCoeff_zero hex0`.
-/
theorem pt_zero (hex0 : PowerSeries.constantCoeff ex = 0) : pt ex (0 : MvPowerSeries σ ℂ_[p]) = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero hex0

/- English proof (translation)
The claim follows from `PowerSeries.subst_zero_of_constantCoeff_zero hl0`.
-/
theorem lg_zero (hl0 : PowerSeries.constantCoeff l = 0) : lg l (0 : MvPowerSeries σ ℂ_[p]) = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero hl0

end Ops

section Pair

variable {τ : Type*}

def pr (x y : MvPowerSeries τ ℂ_[p]) (f : MvPowerSeries (Fin 2) ℂ_[p]) : MvPowerSeries τ ℂ_[p] :=
  MvPowerSeries.subst ![x, y] f

/- English proof (translation)
Introduce `i`. Use `fin_cases i`. Use `exacts [hx, hy]`.
-/
private theorem forall_fin_two_vec_of_both {α : Type*} (P : α → Prop) {x y : α} (hx : P x) (hy : P y) :
    ∀ i : Fin 2, P (![x, y] i) := by
  intro i
  fin_cases i
  exacts [hx, hy]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)`.
-/
theorem hasSubst_pr {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.HasSubst ![x, y] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)

/- English proof (translation)
Use `show MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] f) = 0`. Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pr hx hy) (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy) hf`.
-/
theorem cc_pr {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) {f : MvPowerSeries (Fin 2) ℂ_[p]}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (pr x y f) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] f) = 0
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pr hx hy)
    (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy) hf

/- English proof (translation)
Unfold `pr`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_pr hx hy) hb]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem pr_comp {υ : Type*} {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst b (pr x y f) = pr (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) f := by
  unfold pr
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pr hx hy) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Use `show MvPowerSeries.subst ![x, y] f ∈ PI.AddIntG.Wk.SerS S τ`. Conclude with `PI.AddIntG.Wk.mvsubst_mem_SerS S (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy) (forall_fin_two_vec_of_both (fun z => z ∈ PI.AddIntG.Wk.SerS S τ) hxS hyS) hf`.
-/
theorem pr_mem {S : Subring ℂ_[p]} {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hxS : x ∈ SerS S τ) (hyS : y ∈ SerS S τ)
    {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : f ∈ SerS S (Fin 2)) : pr x y f ∈ SerS S τ := by
  show MvPowerSeries.subst ![x, y] f ∈ PI.AddIntG.Wk.SerS S τ
  exact PI.AddIntG.Wk.mvsubst_mem_SerS S (forall_fin_two_vec_of_both (fun z => MvPowerSeries.constantCoeff z = 0) hx hy)
    (forall_fin_two_vec_of_both (fun z => z ∈ PI.AddIntG.Wk.SerS S τ) hxS hyS) hf

/- English proof (translation)
Establish `hg : MvPowerSeries.constantCoeff (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) = 0`. Rewrite using `[map_sub, MvPowerSeries.constantCoeff_C, sub_self]`. Establish `h` using `MvPowerSeries.constantCoeff_subst_eq_zero hA ha hg`. Rewrite `h` using `[MvPowerSeries.subst_sub hA, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C, sub_eq_zero]`. Conclude with `h`.
-/
theorem cc_subst_eq {σ : Type*} {a : σ → MvPowerSeries τ ℂ_[p]} (hA : MvPowerSeries.HasSubst a)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hg : MvPowerSeries.constantCoeff (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h := MvPowerSeries.constantCoeff_subst_eq_zero hA ha hg
  rw [MvPowerSeries.subst_sub hA, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C,
    sub_eq_zero] at h
  exact h

/- English proof (translation)
Establish `hb` using `hasSubst_pr hx hy`. Rewrite using `[pr, subst_add hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _), MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression.
-/
theorem add_pr {l ex : PowerSeries ℂ_[p]} (hl : PowerSeries.constantCoeff l = 0)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    add l ex x y = pr x y (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_add hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

/- English proof (translation)
Establish `hb` using `hasSubst_pr hx hy`. Rewrite using `[pr, subst_sub hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _), MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression.
-/
theorem sub_pr {l ex : PowerSeries ℂ_[p]} (hl : PowerSeries.constantCoeff l = 0)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    sub l ex x y = pr x y (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_sub hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

end Pair

end PI.FglTriFactor.Wk
