import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh

namespace GlobalTheory.WeightFrobenius

open MvPowerSeries

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.PGsh.OrdGe`. Conclude with `Iff.rfl`.
-/
private theorem ordGe_iff_forall_le_valuation_coeff {f : MvPowerSeries (Fin M) C} {w : ℝ} :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w ↔
      ∀ α : Fin M →₀ ℕ, ((w - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) ≤ v (coeff α f) := by
  unfold _root_.ReciprocityTheory.PGsh.OrdGe
  exact Iff.rfl

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite `*` using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Rewrite using `[map_add]`. Conclude with `le_trans (le_min (hf α) (hg α)) (v.map_add _ _)`.
-/
private theorem ordGe_add' {f g : MvPowerSeries (Fin M) C} {w : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f + g) w := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [map_add]
  exact le_trans (le_min (hf α) (hg α)) (v.map_add _ _)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Simplify using the standard rewrite rules.
-/
private theorem ordGe_zero_left {w : ℝ} : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (0 : MvPowerSeries (Fin M) C) w := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  simp

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun g => _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) (fun _ _ => ordGe_add') ordGe_zero_left hf`.
-/
private theorem ordGe_finset_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries (Fin M) C}
    {w : ℝ} (hf : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f i) w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (∑ i ∈ s, f i) w :=
  Finset.sum_induction f (fun g => _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) (fun _ _ => ordGe_add')
    ordGe_zero_left hf

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite `*` using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Rewrite using `[← map_natCast (MvPowerSeries.C : C →+* MvPowerSeries (Fin M) C) c, coeff_mul_C, AddValuation.map_mul]`. Establish `h : ((w + t - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) = ((w - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) + (t : WithTop ℝ)`. Rewrite using `[← WithTop.coe_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `add_le_add (hf α) hc`.
-/
private theorem ordGe_mul_natCast_of_le_valuation {f : MvPowerSeries (Fin M) C} {w t : ℝ} {c : ℕ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hc : (t : WithTop ℝ) ≤ v (c : C)) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f * (c : MvPowerSeries (Fin M) C)) (w + t) := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [← map_natCast (MvPowerSeries.C : C →+* MvPowerSeries (Fin M) C) c, coeff_mul_C,
    AddValuation.map_mul]
  have h : ((w + t - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) =
      ((w - ∑ m, ρ m * (α m : ℝ) : ℝ) : WithTop ℝ) + (t : WithTop ℝ) := by
    rw [← WithTop.coe_add]
    congr 1
    ring
  rw [h]
  exact add_le_add (hf α) hc

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite `*` using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Rewrite using `[coeff_mul]`. Use `AddValuation.map_le_sum v fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Substitute `hp` using the available equality. Rewrite using `[AddValuation.map_mul]`. Establish `h : ((a + b - ∑ m, ρ m * ((p.1 + p.2) m : ℝ) : ℝ) : WithTop ℝ) = ((a - ∑ m, ρ m * (p.1 m : ℝ) : ℝ) : WithTop ℝ) + ((b - ∑ m, ρ m * (p.2 m : ℝ) : ℝ) : WithTop ℝ)`. Rewrite using `[← WithTop.coe_add]`. Use `congr 1`.

Simplify using `only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `add_le_add (hf _) (hg _)`.
-/
private theorem ordGe_mul' {f g : MvPowerSeries (Fin M) C} {a b : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f a) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g b) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f * g) (a + b) := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  rw [coeff_mul]
  refine AddValuation.map_le_sum v fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  rw [AddValuation.map_mul]
  have h : ((a + b - ∑ m, ρ m * ((p.1 + p.2) m : ℝ) : ℝ) : WithTop ℝ) =
      ((a - ∑ m, ρ m * (p.1 m : ℝ) : ℝ) : WithTop ℝ) +
        ((b - ∑ m, ρ m * (p.2 m : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add]
    congr 1
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [h]
  exact add_le_add (hf _) (hg _)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Rewrite using `[coeff_one]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem ordGe_one_zero : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0 := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (ordGe_one_zero : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0)`. Consider the case `succ n ih`. Rewrite using `[pow_succ, show ((n + 1 : ℕ) : ℝ) * a = n * a + a by push_cast; ring]`. Conclude with `ordGe_mul' ih hf`.
-/
private theorem ordGe_pow_unramified_depth {f : MvPowerSeries (Fin M) C} {a : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f a) (n : ℕ) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using (ordGe_one_zero : _root_.ReciprocityTheory.PGsh.OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0)
  | succ n ih =>
    rw [pow_succ, show ((n + 1 : ℕ) : ℝ) * a = n * a + a by push_cast; ring]
    exact ordGe_mul' ih hf

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Establish `hm` using `_root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (m : ℤ)`. Rewrite `hm` using `[Int.cast_natCast]`. Rewrite using `[Nat.cast_mul, AddValuation.map_mul, hv]`. Simplify `add_le_add_left hm (1 : WithTop ℝ)` using `[add_comm]`.
-/
private theorem one_le_valuation_natCast_of_dvd_of_valuation_eq_one {l c : ℕ} (hv : v (l : C) = 1) (h : l ∣ c) :
    ((1 : ℝ) : WithTop ℝ) ≤ v (c : C) := by
  obtain ⟨m, rfl⟩ := h
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (m : ℤ)
  rw [Int.cast_natCast] at hm
  rw [Nat.cast_mul, AddValuation.map_mul, hv]
  simpa [add_comm] using add_le_add_left hm (1 : WithTop ℝ)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite `*` using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Conclude with `le_trans (WithTop.coe_le_coe.2 (by linarith)) (hf α)`.
-/
private theorem ordGe_mono' {f : MvPowerSeries (Fin M) C} {w w' : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hw : w' ≤ w) : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w' := by
  rw [ordGe_iff_forall_le_valuation_coeff] at *
  intro α
  exact le_trans (WithTop.coe_le_coe.2 (by linarith)) (hf α)

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, l ^ k = n + 1` from `⟨l ^ k - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos k)).symm⟩`. Establish `hlk : (l : ℝ) ^ k = n + 1` using `by exact_mod_cast hn`. Rewrite using `[hlk, hn]`. Establish `key : (f + g) ^ (n + 1) - f ^ (n + 1) - g ^ (n + 1) = ∑ i ∈ Finset.range n, f ^ (i + 1) * g ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1) : MvPowerSeries (Fin M) C)`. Rewrite using `[add_pow, Finset.sum_range_succ, Finset.sum_range_succ']`.

Simplify using `only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero, Nat.cast_one, mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Use `ordGe_finset_sum _ fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < n` using `Finset.mem_range.1 hi`.

Establish `hdvd : l ∣ (n + 1).choose (i + 1)`. Rewrite using `[← hn]`. Conclude with `hl.dvd_choose_pow (Nat.succ_ne_zero i) (by omega)`. Establish `h` using `ordGe_mul_natCast_of_le_valuation (ordGe_mul' (ordGe_pow_unramified_depth hf (i + 1)) (ordGe_pow_unramified_depth hg (n + 1 - (i + 1)))) (one_le_valuation_natCast_of_dvd_of_valuation_eq_one hv hdvd)`. Use `ordGe_mono' h (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one {l k : ℕ} (hl : l.Prime)
    (hv : v (l : C) = 1) {f g : MvPowerSeries (Fin M) C} {w : ℝ}
    (hf : _root_.ReciprocityTheory.PGsh.OrdGe v ρ f w) (hg : _root_.ReciprocityTheory.PGsh.OrdGe v ρ g w) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((f + g) ^ (l ^ k) - f ^ (l ^ k) - g ^ (l ^ k)) (1 + (l : ℝ) ^ k * w) := by
  obtain ⟨n, hn⟩ : ∃ n, l ^ k = n + 1 := ⟨l ^ k - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos k)).symm⟩
  have hlk : (l : ℝ) ^ k = n + 1 := by exact_mod_cast hn
  rw [hlk, hn]
  have key : (f + g) ^ (n + 1) - f ^ (n + 1) - g ^ (n + 1) = ∑ i ∈ Finset.range n,
      f ^ (i + 1) * g ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1) : MvPowerSeries (Fin M) C) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero,
      Nat.cast_one, mul_one, one_mul]
    abel
  rw [key]
  refine ordGe_finset_sum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  have hdvd : l ∣ (n + 1).choose (i + 1) := by
    rw [← hn]
    exact hl.dvd_choose_pow (Nat.succ_ne_zero i) (by omega)
  have h := ordGe_mul_natCast_of_le_valuation
    (ordGe_mul' (ordGe_pow_unramified_depth hf (i + 1)) (ordGe_pow_unramified_depth hg (n + 1 - (i + 1))))
    (one_le_valuation_natCast_of_dvd_of_valuation_eq_one hv hdvd)
  refine ordGe_mono' h (le_of_eq ?_)
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero k hl.ne_zero), sub_zero]`. Conclude with `ordGe_zero_left`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `hxa` using `hx a (Finset.mem_insert_self a s)`. Establish `hxs : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x i) w` using `fun i hi => hx i (Finset.mem_insert_of_mem hi)`. Establish `h` using `ordGe_add' (ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hxa (ordGe_finset_sum s hxs)) (ih hxs)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordGe_sum_pow_sub_sum_pow_of_valuation_eq_one {l k : ℕ} (hl : l.Prime)
    (hv : v (l : C) = 1) {ι : Type} (s : Finset ι) {x : ι → MvPowerSeries (Fin M) C} {w : ℝ}
    (hx : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x i) w) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((∑ i ∈ s, x i) ^ (l ^ k) - ∑ i ∈ s, x i ^ (l ^ k)) (1 + (l : ℝ) ^ k * w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero k hl.ne_zero), sub_zero]
    exact ordGe_zero_left
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x i) w := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := ordGe_add' (ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hxa
      (ordGe_finset_sum s hxs)) (ih hxs)
    convert h using 1
    ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Establish `hS` using `ordGe_finset_sum Finset.univ fun j _ => hx j`. Establish `h₁` using `ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hS (ordGe_mono' hν hw)`. Establish `h₂` using `ordGe_pow_unramified_depth hν (l ^ k)`. Establish `h₃` using `ordGe_sum_pow_sub_sum_pow_of_valuation_eq_one (k := k) hl hv Finset.univ fun j _ => hx j`. Move the coercions through the operations in `at h₂`.

Establish `h` using `ordGe_add' (ordGe_add' (ordGe_mono' h₁ (min_le_left _ _)) (ordGe_mono' h₂ (min_le_right _ _))) (ordGe_mono' h₃ (min_le_left _ _))`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordGe_sum_add_pow_sub_sum_pow_ge_min {l k : ℕ} (hl : l.Prime) (hv : v (l : C) = 1)
    {x : Fin M → MvPowerSeries (Fin M) C} {ν : MvPowerSeries (Fin M) C} {w w₂ : ℝ}
    (hw : w ≤ w₂) (hx : ∀ j, _root_.ReciprocityTheory.PGsh.OrdGe v ρ (x j) w) (hν : _root_.ReciprocityTheory.PGsh.OrdGe v ρ ν w₂) :
    _root_.ReciprocityTheory.PGsh.OrdGe v ρ ((∑ j, x j + ν) ^ (l ^ k) - ∑ j, x j ^ (l ^ k))
      (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂)) := by
  have hS := ordGe_finset_sum Finset.univ fun j _ => hx j
  have h₁ := ordGe_add_pow_sub_pow_sub_pow_of_valuation_eq_one (k := k) hl hv hS
    (ordGe_mono' hν hw)
  have h₂ := ordGe_pow_unramified_depth hν (l ^ k)
  have h₃ := ordGe_sum_pow_sub_sum_pow_of_valuation_eq_one (k := k) hl hv Finset.univ fun j _ => hx j
  push_cast at h₂
  have h := ordGe_add' (ordGe_add' (ordGe_mono' h₁ (min_le_left _ _))
    (ordGe_mono' h₂ (min_le_right _ _))) (ordGe_mono' h₃ (min_le_left _ _))
  convert h using 1
  ring

open MvPowerSeries in
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ} in
/- English proof (translation)
Rewrite using `[ordGe_iff_forall_le_valuation_coeff]`. Introduce `α`. Rewrite using `[coeff_C_mul, coeff_X_pow]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify `ha` using `[Finsupp.single_apply]`. Simplify using the standard rewrite rules.
-/
private theorem ordGe_C_mul_X_pow_of_le_valuation {r w : ℝ} {a : C} (j : Fin M) (N : ℕ)
    (ha : ((w - r * N : ℝ) : WithTop ℝ) ≤ v a) :
    _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r)
      (MvPowerSeries.C (R := C) a * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) w := by
  rw [ordGe_iff_forall_le_valuation_coeff]
  intro α
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h
    simpa [Finsupp.single_apply] using ha
  · simp

open MvPowerSeries in
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) in
/- English proof (translation)
Introduce `C _ _ v l hl hv M N k r w w₂ a ν hw ha hν`. Rewrite using `[show (∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) = ∑ j, (MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) ^ (l ^ k) from Finset.sum_congr rfl fun j _ => by rw [mul_pow, ← map_pow …`. Conclude with `ordGe_sum_add_pow_sub_sum_pow_ge_min hl hv hw (fun j => ordGe_C_mul_X_pow_of_le_valuation j N (ha j)) hν`.
-/
theorem _root_.GlobalTheory.WeightFrobenius.main :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (M N k : ℕ) (r w w₂ : ℝ) (a : Fin M → C) (ν : MvPowerSeries (Fin M) C), w ≤ w₂ → (∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) →
    _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r) ν w₂ → _root_.ReciprocityTheory.PGsh.OrdGe v (fun _ => r) ((∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N + ν) ^ (l ^ k) -
      ∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂))) := by
  intro C _ _ v l hl hv M N k r w w₂ a ν hw ha hν
  rw [show (∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) *
      (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) =
      ∑ j, (MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N) ^ (l ^ k)
    from Finset.sum_congr rfl fun j _ => by rw [mul_pow, ← map_pow, ← pow_mul]]
  exact ordGe_sum_add_pow_sub_sum_pow_ge_min hl hv hw (fun j => ordGe_C_mul_X_pow_of_le_valuation j N (ha j)) hν

end GlobalTheory.WeightFrobenius
