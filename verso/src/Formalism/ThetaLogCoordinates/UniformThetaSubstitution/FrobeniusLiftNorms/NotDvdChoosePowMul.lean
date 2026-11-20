import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace LemOne

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Proceed by induction on `k with`. Consider the case `zero => simpa using hm`. Consider the case `succ k ih`. Introduce `h`.

Apply `ih` to reduce the goal to its premises. Establish `key` using `Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p ^ (k + 1) * m) (k := p ^ (k + 1))`. Establish `e1 : p ^ (k + 1) * m % p = 0`. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `Nat.mul_mod_right _ _`.

Establish `e2 : p ^ (k + 1) % p = 0`. Rewrite using `[pow_succ']`. Conclude with `Nat.mul_mod_right _ _`. Establish `e3 : p ^ (k + 1) * m / p = p ^ k * m`. Rewrite using `[pow_succ', mul_assoc]`.

Conclude with `Nat.mul_div_cancel_left _ hp.pos`. Establish `e4 : p ^ (k + 1) / p = p ^ k`. Rewrite using `[pow_succ']`. Conclude with `Nat.mul_div_cancel_left _ hp.pos`. Rewrite `key` using `[e1, e2, e3, e4, Nat.choose_self, one_mul]`.

Conclude with `(key.dvd_iff dvd_rfl).1 h`.
-/
theorem not_dvd_choose_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ k * m).choose (p ^ k) := by
  have := Fact.mk hp
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    intro h
    apply ih
    have key := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p ^ (k + 1) * m)
      (k := p ^ (k + 1))
    have e1 : p ^ (k + 1) * m % p = 0 := by
      rw [pow_succ', mul_assoc]; exact Nat.mul_mod_right _ _
    have e2 : p ^ (k + 1) % p = 0 := by
      rw [pow_succ']; exact Nat.mul_mod_right _ _
    have e3 : p ^ (k + 1) * m / p = p ^ k * m := by
      rw [pow_succ', mul_assoc]; exact Nat.mul_div_cancel_left _ hp.pos
    have e4 : p ^ (k + 1) / p = p ^ k := by
      rw [pow_succ']; exact Nat.mul_div_cancel_left _ hp.pos
    rw [e1, e2, e3, e4, Nat.choose_self, one_mul] at key
    exact (key.dvd_iff dvd_rfl).1 h

/- English proof (translation)
Take `⟨k, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one`. Use `⟨p ^ k, pow_pos hp.pos k, ?_, not_dvd_choose_pow_mul hp k m hm⟩` and prove the remaining obligations. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero _)`. Establish `hm1 : m ≠ 1` using `by rintro rfl; exact hpow k (by simp)`. Establish `: 2 ≤ m` using `by omega`.

Establish `hpos` using `pow_pos hp.pos k`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_not_dvd_choose {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n)
    (hpow : ∀ k, n ≠ p ^ k) : ∃ i, 0 < i ∧ i < n ∧ ¬ p ∣ n.choose i := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  refine ⟨p ^ k, pow_pos hp.pos k, ?_, not_dvd_choose_pow_mul hp k m hm⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : m ≠ 1 := by rintro rfl; exact hpow k (by simp)
  have : 2 ≤ m := by omega
  have hpos := pow_pos hp.pos k
  nlinarith

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hle : p ^ k ≤ p ^ (k + 1)` using `Nat.pow_le_pow_right hp.pos (Nat.le_succ k)`. Establish `h` using `hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_pos hp.pos k).ne'`. Establish `hc : (p ^ (k + 1)).choose (p ^ k) ≠ 0` using `(Nat.choose_pos hle).ne'`. Rewrite `h` using `[← padicValNat_eq_emultiplicity hc, ← padicValNat_eq_emultiplicity (pow_pos hp.pos k).ne', padicValNat.prime_pow]`.

Establish `h' : padicValNat p ((p ^ (k + 1)).choose (p ^ k)) + k = k + 1` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValNat_choose_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    padicValNat p ((p ^ (k + 1)).choose (p ^ k)) = 1 := by
  have := Fact.mk hp
  have hle : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
  have h := hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_pos hp.pos k).ne'
  have hc : (p ^ (k + 1)).choose (p ^ k) ≠ 0 := (Nat.choose_pos hle).ne'
  rw [← padicValNat_eq_emultiplicity hc, ← padicValNat_eq_emultiplicity (pow_pos hp.pos k).ne',
    padicValNat.prime_pow] at h
  have h' : padicValNat p ((p ^ (k + 1)).choose (p ^ k)) + k = k + 1 := by exact_mod_cast h
  omega

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hf _) (norm_nonneg _) (hg _)`.
-/
theorem integral_mul {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `n`. Rewrite using `[pow_zero, MvPowerSeries.coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ d ih => rw [pow_succ]`. Conclude with `integral_mul ih hf`.
-/
theorem integral_pow {ι : Type} {f : MvPowerSeries ι K} (hf : Integral f) (d : ℕ) :
    Integral (f ^ d) := by
  classical
  induction d with
  | zero =>
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ d ih => rw [pow_succ]; exact integral_mul ih hf

end Norm

section Top

variable {K : Type} [Field K]

/- English proof (translation)
Use `MvPowerSeries.nat_le_order fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : d.degree = d 0 + d 1`. Rewrite using `[Finsupp.degree_eq_sum, Fin.sum_univ_two]`. Rewrite using `[map_sub, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]`. Break down `Nat.lt_or_ge d.degree 1 with h0 | h1` into its components or cases.

Establish `hd0 : d = 0`. Use extensionality with `x`. Use `fin_cases x`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Substitute `hd0` using the available equality. Establish `: MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F = 0`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Conclude with `hF0`. Rewrite using `[this, if_neg, if_neg]`. Simplify using the standard rewrite rules. Introduce `h`. Use `congrArg (fun e => e 1) h` as an intermediate fact.

Simplify using `at this`. Introduce `h`. Use `congrArg (fun e => e 0) h` as an intermediate fact. Simplify using `at this`. Establish `hd1 : d.degree = 1` using `by omega`.

Rewrite using `[hF1 d hd1]`. Distinguish the cases in `h : d 0 = 1`. Establish `: d = Finsupp.single 0 1`. Use extensionality with `x`. Use `fin_cases x`.

Simplify using `using h`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Rewrite using `[if_pos rfl, if_neg]`.

Simplify using the standard rewrite rules. Introduce `h`. Use `congrArg (fun e => e 1) h` as an intermediate fact. Simplify using `at this`. Establish `: d = Finsupp.single 1 1`.

Use extensionality with `x`. Use `fin_cases x`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Rewrite using `[if_pos rfl, if_neg]`. Simplify using the standard rewrite rules. Introduce `h`.

Use `congrArg (fun e => e 1) h` as an intermediate fact. Simplify using `at this`.
-/
theorem order_sub_lin {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) :
    ((2 : ℕ) : ℕ∞) ≤ (F - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).order := by
  classical
  refine MvPowerSeries.nat_le_order fun d hd => ?_
  have hdeg : d.degree = d 0 + d 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [map_sub, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · have hd0 : d = 0 := by
      ext x; fin_cases x
      · simp; omega
      · simp; omega
    subst hd0
    have : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hF0
    rw [this, if_neg, if_neg]
    · simp
    · intro h; have := congrArg (fun e => e 1) h; simp at this
    · intro h; have := congrArg (fun e => e 0) h; simp at this
  · have hd1 : d.degree = 1 := by omega
    rw [hF1 d hd1]
    by_cases h : d 0 = 1
    · have : d = Finsupp.single 0 1 := by
        ext x; fin_cases x
        · simpa using h
        · simp; omega
      subst this
      rw [if_pos rfl, if_neg]
      · simp
      · intro h; have := congrArg (fun e => e 1) h; simp at this
    · have : d = Finsupp.single 1 1 := by
        ext x; fin_cases x
        · simp; omega
        · simp; omega
      subst this
      rw [if_pos rfl, if_neg]
      · simp
      · intro h; have := congrArg (fun e => e 1) h; simp at this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : F ^ (n + 1) - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ (n + 1) = F * (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n) + (F - (MvPowerSeries.X 0 + MvPowerSeries.X 1)) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n` using `by ring`. Rewrite using `[e]`.

Use `le_trans (le_min ?_ ?_) MvPowerSeries.min_order_le_add` and prove the remaining obligations. Use `le_trans ?_ MvPowerSeries.le_order_mul` and prove the remaining obligations. Establish `h1 : (1 : ℕ∞) ≤ F.order` using `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hF0`. Combine the equalities or inequalities in the displayed calculation. Use `le_trans ?_ MvPowerSeries.le_order_mul` and prove the remaining obligations.

Establish `h2` using `order_sub_lin hF0 hF1`. Establish `h3 : (n : ℕ∞) ≤ ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ n).order` using `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n (by simp)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem order_pow_sub_lin {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : F ^ (n + 1) - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ (n + 1) =
        F * (F ^ n - (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n) +
          (F - (MvPowerSeries.X 0 + MvPowerSeries.X 1)) *
            (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ n := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) MvPowerSeries.min_order_le_add
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      have h1 : (1 : ℕ∞) ≤ F.order := MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hF0
      calc ((n + 1 + 1 : ℕ) : ℕ∞) = 1 + ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ _ := add_le_add h1 ih
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      have h2 := order_sub_lin hF0 hF1
      have h3 : (n : ℕ∞) ≤ ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ n).order :=
        MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n (by simp)
      calc ((n + 1 + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) + (n : ℕ∞) := by push_cast; ring
        _ ≤ _ := add_le_add h2 h3

/- English proof (translation)
Rewrite using `[map_add, Finsupp.degree_single, Finsupp.degree_single]`.
-/
theorem degree_pair (i j : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j).degree = i + j := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

/- English proof (translation)
Rewrite using `[add_pow, map_sum, Finset.sum_eq_single i]`. Rewrite using `[← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial_same]`. Simplify using the standard rewrite rules. Introduce `m _ hm`. Rewrite using `[← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial, if_neg, zero_mul]`.

Introduce `h`. Apply `hm` to reduce the goal to its premises. Use `congrArg (fun e => e 0) h` as an intermediate fact. Simplify using `using this.symm`. Introduce `h`.

Conclude with `absurd (mem_range.mpr (by omega)) h`.
-/
theorem coeff_lin_pow (n i : ℕ) (hi : i ≤ n) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i))
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ n) = (n.choose i : K) := by
  classical
  rw [add_pow, map_sum, Finset.sum_eq_single i]
  · rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial_same]
    simp
  · intro m _ hm
    rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
      MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.coeff_monomial, if_neg, zero_mul]
    intro h
    apply hm
    have := congrArg (fun e => e 0) h
    simpa using this.symm
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/- English proof (translation)
Rewrite using `[← coeff_lin_pow (K := K) n i hi, ← sub_eq_zero, ← map_sub]`. Use `MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_pow_sub_lin hF0 hF1 n))` and prove the remaining obligations. Rewrite using `[degree_pair]`. Establish `: i + (n - i) = n` using `by omega`. Rewrite using `[this]`.

Conclude with `Nat.lt_succ_self n` after adjusting the coercions.
-/
theorem coeff_pow_top {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) (n i : ℕ) (hi : i ≤ n) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i))
      (F ^ n) = (n.choose i : K) := by
  rw [← coeff_lin_pow (K := K) n i hi, ← sub_eq_zero, ← map_sub]
  refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_pow_sub_lin hF0 hF1 n))
  rw [degree_pair]
  have : i + (n - i) = n := by omega
  rw [this]
  exact_mod_cast Nat.lt_succ_self n

end Top

section Main

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max x (-y)`.
-/
theorem norm_sub_le_max (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max x (-y)

/- English proof (translation)
Take `⟨e, he⟩ : ∃ e : Fin 2 →₀ ℕ, e = Finsupp.single 0 i + Finsupp.single 1 (n - i)` from `⟨_, rfl⟩`. Establish `hdeg : e.degree = n` using `by rw [he, degree_pair]; omega`. Establish `hs : PowerSeries.HasSubst F` using `PowerSeries.HasSubst.of_constantCoeff_zero hF0`. Establish `e0 : e 0 = i` using `by simp [he]`. Establish `e1 : e 1 = n - i` using `by simp [he]`.

Establish `h0 : MvPowerSeries.coeff e (at1 0 h) = 0`. Rewrite using `[coeff_single_variable_series, if_neg]`. Introduce `hh`. Use `congrArg (fun u => u 1) hh` as an intermediate fact. Simplify using `[e1] at this`.

Use linear arithmetic over natural numbers and integers. Establish `h1 : MvPowerSeries.coeff e (at1 1 h) = 0`. Rewrite using `[coeff_single_variable_series, if_neg]`. Introduce `hh`. Use `congrArg (fun u => u 0) hh` as an intermediate fact.

Simplify using `[e0] at this`. Use linear arithmetic over natural numbers and integers. Establish `key : MvPowerSeries.coeff e (PowerSeries.subst F h) = ∑ d ∈ range (n + 1), PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d)`. Rewrite using `[PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := range (n + 1))]`. Simplify using `only [smul_eq_mul]`.

Introduce `d hd`. Rewrite `hd` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hlt`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[MvPowerSeries.coeff_of_lt_order, smul_zero]`. Use `lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hF0)` and prove the remaining obligations. Rewrite using `[hdeg]`. Conclude with `(by omega : n < d)` after adjusting the coercions. Establish `htop : MvPowerSeries.coeff e (F ^ n) = (n.choose i : K)`.

Rewrite using `[he]`. Conclude with `coeff_pow_top hF0 hF1 n i hin.le`. Establish `hc` using `hcob e`. Unfold `cob at hc`. Rewrite `hc` using `[map_sub, map_sub, h0, h1, sub_zero, sub_zero, key, sum_range_succ, htop]`.

Establish `hsum : ‖∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d)‖ ≤ 1`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d hd => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hlow d (mem_range.1 hd)) (norm_nonneg _) (integral_pow hFi d e)`. Establish `hsplit : PowerSeries.coeff n h * (n.choose i : K) = (∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) + PowerSeries.coeff n h * (n.choose i : K)) - ∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d)` using `by ring`.

Rewrite using `[hsplit]`. Conclude with `(norm_sub_le_max _ _).trans (max_le hc hsum)`.
-/
theorem norm_coeff_mul_choose {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) {n : ℕ}
    (hlow : ∀ d < n, ‖PowerSeries.coeff d h‖ ≤ 1) {i : ℕ} (hi0 : 0 < i) (hin : i < n) :
    ‖PowerSeries.coeff n h * (n.choose i : K)‖ ≤ 1 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin 2 →₀ ℕ, e = Finsupp.single 0 i + Finsupp.single 1 (n - i) := ⟨_, rfl⟩
  have hdeg : e.degree = n := by rw [he, degree_pair]; omega
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have e0 : e 0 = i := by simp [he]
  have e1 : e 1 = n - i := by simp [he]
  have h0 : MvPowerSeries.coeff e (at1 0 h) = 0 := by
    rw [coeff_single_variable_series, if_neg]
    intro hh
    have := congrArg (fun u => u 1) hh
    simp [e1] at this
    omega
  have h1 : MvPowerSeries.coeff e (at1 1 h) = 0 := by
    rw [coeff_single_variable_series, if_neg]
    intro hh
    have := congrArg (fun u => u 0) hh
    simp [e0] at this
    omega
  have key : MvPowerSeries.coeff e (PowerSeries.subst F h) =
      ∑ d ∈ range (n + 1), PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) := by
    rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := range (n + 1))]
    · simp only [smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hd
      rw [MvPowerSeries.coeff_of_lt_order, smul_zero]
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hF0)
      rw [hdeg]
      exact_mod_cast (by omega : n < d)
  have htop : MvPowerSeries.coeff e (F ^ n) = (n.choose i : K) := by
    rw [he]; exact coeff_pow_top hF0 hF1 n i hin.le
  have hc := hcob e
  unfold cob at hc
  rw [map_sub, map_sub, h0, h1, sub_zero, sub_zero, key, sum_range_succ, htop] at hc
  have hsum : ‖∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d hd => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hlow d (mem_range.1 hd)) (norm_nonneg _) (integral_pow hFi d e)
  have hsplit : PowerSeries.coeff n h * (n.choose i : K) =
      (∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) +
        PowerSeries.coeff n h * (n.choose i : K)) -
      ∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) := by ring
  rw [hsplit]
  exact (norm_sub_le_max _ _).trans (max_le hc hsum)

/- English proof (translation)
Rewrite using `[hnp]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`.
-/
theorem norm_p_lt_one {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) : ‖(p : K)‖ < 1 := by
  rw [hnp]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/- English proof (translation)
Take `⟨i, hi0, hin, hnd⟩` from `exists_not_dvd_choose hp hn hpow`. Use `norm_coeff_mul_choose hF0 hFi hF1 hcob hlow hi0 hin` as an intermediate fact. Rewrite `this` using `[norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (norm_p_lt_one hp hnp) hnd, mul_one]`. Then use the resulting hypothesis.
-/
theorem norm_coeff_of_not_pow {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) {n : ℕ} (hn : 2 ≤ n)
    (hpow : ∀ k, n ≠ p ^ k) (hlow : ∀ d < n, ‖PowerSeries.coeff d h‖ ≤ 1) :
    ‖PowerSeries.coeff n h‖ ≤ 1 := by
  obtain ⟨i, hi0, hin, hnd⟩ := exists_not_dvd_choose hp hn hpow
  have := norm_coeff_mul_choose hF0 hFi hF1 hcob hlow hi0 hin
  rwa [norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp (norm_p_lt_one hp hnp) hnd,
    mul_one] at this

/- English proof (translation)
Establish `hlt : p ^ k < p ^ (k + 1)` using `Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)`. Use `norm_coeff_mul_choose hF0 hFi hF1 hcob hlow (pow_pos hp.pos k) hlt` as an intermediate fact. Rewrite `this` using `[norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp (norm_p_lt_one hp hnp) (Nat.choose_pos hlt.le).ne', padicValNat_choose_pow hp k, pow_one, mul_comm, ← norm_mul]`. Then use the resulting hypothesis.
-/
theorem norm_coeff_of_pow {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) (k : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 := by
  have hlt : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)
  have := norm_coeff_mul_choose hF0 hFi hF1 hcob hlow (pow_pos hp.pos k) hlt
  rwa [norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp (norm_p_lt_one hp hnp)
    (Nat.choose_pos hlt.le).ne', padicValNat_choose_pow hp k, pow_one, mul_comm, ← norm_mul] at this

/- English proof (translation)
Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `hd`. Distinguish the cases in `hdk : d ≤ p ^ k`.

Conclude with `hlow d hdk`. Establish `hk1 : 1 ≤ p ^ k` using `pow_pos hp.pos k`. Use `norm_coeff_of_not_pow hp hnp hF0 hFi hF1 hcob (by omega) ?_ fun d' hd' => ih d' hd' (lt_trans hd' hd)` and prove the remaining obligations. Introduce and unpack `m rfl`. Establish `h1 : k < m` using `(Nat.pow_lt_pow_iff_right hp.one_lt).1 (not_le.1 hdk)`.

Establish `h2 : m < k + 1` using `(Nat.pow_lt_pow_iff_right hp.one_lt).1 hd`. Use linear arithmetic over natural numbers and integers.
-/
theorem low_up {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) (k : ℕ)
    (hlow : ∀ d ≤ p ^ k, ‖PowerSeries.coeff d h‖ ≤ 1) :
    ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    by_cases hdk : d ≤ p ^ k
    · exact hlow d hdk
    · have hk1 : 1 ≤ p ^ k := pow_pos hp.pos k
      refine norm_coeff_of_not_pow hp hnp hF0 hFi hF1 hcob (by omega) ?_
        fun d' hd' => ih d' hd' (lt_trans hd' hd)
      rintro m rfl
      have h1 : k < m := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (not_le.1 hdk)
      have h2 : m < k + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
      omega

/- English proof (translation)
Establish `hμ` using `norm_coeff_of_pow hp hnp hF0 hFi hF1 hcob k hlow`. Establish `hp0 : (p : K) ≠ 0`. Introduce `h0`. Rewrite `hnp` using `[h0, norm_zero]`. Conclude with `(inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp`.

Use `⟨hμ, low_up hp hnp hF0 hFi hF1 hcob' (k + 1) fun d hd => ?_⟩` and prove the remaining obligations. Rewrite using `[hh', map_sub, PowerSeries.coeff_C_mul]`. Break down `lt_or_eq_of_le hd with hlt | rfl` into its components or cases. Use `(norm_sub_le_max _ _).trans (max_le (hlow d hlt) ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc, norm_mul]`.

Conclude with `mul_le_one₀ hμ (norm_nonneg _) (hglow d hlt)`. Rewrite using `[hgtop]`. Establish `: PowerSeries.coeff (p ^ (k + 1)) h - (p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j * ((p : K) ^ (j + 1))⁻¹ = 0`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, norm_zero]`. Conclude with `zero_le_one`.
-/
theorem correct {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h g h' : PowerSeries K} (hcob : Integral (cob F h)) (k j : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1)
    (hglow : ∀ d < p ^ (k + 1), ‖(p : K) ^ j * PowerSeries.coeff d g‖ ≤ 1)
    (hgtop : PowerSeries.coeff (p ^ (k + 1)) g = ((p : K) ^ (j + 1))⁻¹)
    (hh' : h' = h - PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j) * g)
    (hcob' : Integral (cob F h')) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 ∧
      ∀ d < p ^ (k + 2), ‖PowerSeries.coeff d h'‖ ≤ 1 := by
  have hμ := norm_coeff_of_pow hp hnp hF0 hFi hF1 hcob k hlow
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  refine ⟨hμ, low_up hp hnp hF0 hFi hF1 hcob' (k + 1) fun d hd => ?_⟩
  rw [hh', map_sub, PowerSeries.coeff_C_mul]
  rcases lt_or_eq_of_le hd with hlt | rfl
  · refine (norm_sub_le_max _ _).trans (max_le (hlow d hlt) ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (hglow d hlt)
  · rw [hgtop]
    have : PowerSeries.coeff (p ^ (k + 1)) h -
        (p : K) * PowerSeries.coeff (p ^ (k + 1)) h * (p : K) ^ j * ((p : K) ^ (j + 1))⁻¹ = 0 := by
      field_simp
      ring
    rw [this, norm_zero]
    exact zero_le_one

/- English proof (translation)
Establish `hp0 : (p : K) ≠ 0`. Introduce `h0`. Rewrite `hnp` using `[h0, norm_zero]`. Conclude with `(inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp`. Distinguish the cases in `hc : PowerSeries.coeff d (g0F K p) = 0`.

Rewrite using `[hc, mul_zero, norm_zero]`. Conclude with `zero_le_one`. Take `⟨i, rfl⟩` from `coeff_g0F_ne_zero hc`. Rewrite using `[coeff_g0F_of K hp.two_le]`. Establish `e : p * (p ^ 2) ^ i = p ^ (2 * i + 1)` using `by ring`.

Rewrite `hd` using `[e]`. Establish `hij : 2 * i + 1 < 2 * j + 1` using `(Nat.pow_lt_pow_iff_right hp.one_lt).1 hd`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le (by omega : i + 1 ≤ j)`. Rewrite using `[pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le`.
-/
theorem g_zero_low_coeff_norm {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (j d : ℕ)
    (hd : d < p ^ (2 * j + 1)) : ‖(p : K) ^ j * PowerSeries.coeff d (g0F K p)‖ ≤ 1 := by
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  by_cases hc : PowerSeries.coeff d (g0F K p) = 0
  · rw [hc, mul_zero, norm_zero]; exact zero_le_one
  · obtain ⟨i, rfl⟩ := coeff_g0F_ne_zero hc
    rw [coeff_g0F_of K hp.two_le]
    have e : p * (p ^ 2) ^ i = p ^ (2 * i + 1) := by ring
    rw [e] at hd
    have hij : 2 * i + 1 < 2 * j + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by omega : i + 1 ≤ j)
    rw [pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le

/- English proof (translation)
Establish `hp0 : (p : K) ≠ 0`. Introduce `h0`. Rewrite `hnp` using `[h0, norm_zero]`. Conclude with `(inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp`. Distinguish the cases in `hc : PowerSeries.coeff d (lgF K p) = 0`.

Rewrite using `[hc, mul_zero, norm_zero]`. Conclude with `zero_le_one`. Take `⟨i, rfl⟩` from `coeff_lgF_ne_zero hc`. Rewrite using `[coeff_lgF_pow K hp.two_le]`. Establish `e : (p ^ 2) ^ i = p ^ (2 * i)` using `by ring`.

Rewrite `hd` using `[e]`. Establish `hij : 2 * i < 2 * j + 2` using `(Nat.pow_lt_pow_iff_right hp.one_lt).1 hd`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le (by omega : i ≤ j)`. Rewrite using `[pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le`.
-/
theorem lg_low {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (j d : ℕ)
    (hd : d < p ^ (2 * j + 2)) : ‖(p : K) ^ j * PowerSeries.coeff d (lgF K p)‖ ≤ 1 := by
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  by_cases hc : PowerSeries.coeff d (lgF K p) = 0
  · rw [hc, mul_zero, norm_zero]; exact zero_le_one
  · obtain ⟨i, rfl⟩ := coeff_lgF_ne_zero hc
    rw [coeff_lgF_pow K hp.two_le]
    have e : (p ^ 2) ^ i = p ^ (2 * i) := by ring
    rw [e] at hd
    have hij : 2 * i < 2 * j + 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by omega : i ≤ j)
    rw [pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst F` using `PowerSeries.HasSubst.of_constantCoeff_zero hF0`. Establish `hx : ∀ x : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K)` using `fun x => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Unfold `cob at1`. Simplify using `only [PowerSeries.subst_sub hs, PowerSeries.subst_mul hs, PowerSeries.subst_sub (hx _), PowerSeries.subst_mul (hx _), PowerSeries.subst_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cob_comb {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (f g l : PowerSeries K) (a b : K) :
    cob F (f - PowerSeries.C a * g - PowerSeries.C b * l) =
      cob F f - MvPowerSeries.C a * cob F g - MvPowerSeries.C b * cob F l := by
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hx : ∀ x : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) :=
    fun x => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold cob at1
  simp only [PowerSeries.subst_sub hs, PowerSeries.subst_mul hs, PowerSeries.subst_sub (hx _),
    PowerSeries.subst_mul (hx _), PowerSeries.subst_C]
  ring

end Main

section Limit

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def rem (p : ℕ) (f : PowerSeries K) (a b : K) : PowerSeries K :=
  f - PowerSeries.C a * g0F K p - PowerSeries.C b * lgF K p

/- English proof (translation)
Unfold `rem`. Rewrite using `[map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]`.
-/
theorem coeff_rem (p : ℕ) (f : PowerSeries K) (a b : K) (n : ℕ) :
    PowerSeries.coeff n (rem p f a b) = PowerSeries.coeff n f - a * PowerSeries.coeff n (g0F K p) -
      b * PowerSeries.coeff n (lgF K p) := by
  unfold rem
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]

/- English proof (translation)
Introduce `n`. Unfold `rem`. Rewrite using `[cob_comb hF0, hFl, mul_zero, sub_zero, map_sub, MvPowerSeries.coeff_C_mul]`. Use `(norm_sub_le_max _ _).trans (max_le (hcob n) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ ha (norm_nonneg _) (hde n)`.
-/
theorem cob_rem_integral {p : ℕ} {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFl : cob F (lgF K p) = 0)
    (hde : Integral (cob F (g0F K p))) {f : PowerSeries K} (hcob : Integral (cob F f))
    {a : K} (ha : ‖a‖ ≤ 1) (b : K) : Integral (cob F (rem p f a b)) := by
  intro n
  unfold rem
  rw [cob_comb hF0, hFl, mul_zero, sub_zero, map_sub, MvPowerSeries.coeff_C_mul]
  refine (norm_sub_le_max _ _).trans (max_le (hcob n) ?_)
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hde n)

def Good (p : ℕ) (f : PowerSeries K) (j : ℕ) (a b : K) : Prop :=
  ‖a‖ ≤ 1 ∧ ∀ d < p ^ (2 * j + 1), ‖PowerSeries.coeff d (rem p f a b)‖ ≤ 1

/- English proof (translation)
Establish `h0 : ‖(0 : K)‖ ≤ 1` using `by rw [norm_zero]; exact zero_le_one`. Use `⟨h0, low_up hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob h0 _) 0 fun d hd => ?_⟩` and prove the remaining obligations. Rewrite `hd` using `[pow_zero]`. Rewrite using `[coeff_rem, zero_mul, sub_zero]`. Establish `hd' : d = 0 ∨ d = 1` using `by omega`.

Break down `hd' with rfl | rfl` into its components or cases. Establish `hl : PowerSeries.coeff 0 (lgF K p) = 0`. Assume the negation of the conclusion as `hc`. Take `⟨i, hi⟩` from `coeff_lgF_ne_zero hc`. Conclude with `(pow_pos (pow_pos hp.pos 2) i).ne hi`.

Rewrite using `[hl, mul_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]`. Conclude with `h0`. Establish `hl : PowerSeries.coeff 1 (lgF K p) = 1`. Use `coeff_lgF_pow K hp.two_le 0` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hl, mul_one, sub_self]`. Conclude with `h0`.
-/
theorem good_zero {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 0) (hcob : Integral (cob F f)) :
    Good p f 0 0 (PowerSeries.coeff 1 f) := by
  have h0 : ‖(0 : K)‖ ≤ 1 := by rw [norm_zero]; exact zero_le_one
  refine ⟨h0, low_up hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob h0 _) 0 fun d hd => ?_⟩
  rw [pow_zero] at hd
  rw [coeff_rem, zero_mul, sub_zero]
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  · have hl : PowerSeries.coeff 0 (lgF K p) = 0 := by
      by_contra hc
      obtain ⟨i, hi⟩ := coeff_lgF_ne_zero hc
      exact (pow_pos (pow_pos hp.pos 2) i).ne hi
    rw [hl, mul_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
    exact h0
  · have hl : PowerSeries.coeff 1 (lgF K p) = 1 := by
      have := coeff_lgF_pow K hp.two_le 0
      simpa using this
    rw [hl, mul_one, sub_self]
    exact h0

/- English proof (translation)
Take `⟨ha, hlow⟩` from `hG`. Establish `hple : ‖(p : K) ^ j‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le`. Take `⟨μ, hμdef⟩ : ∃ μ : K, μ = (p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b)` from `⟨_, rfl⟩`.

Establish `hμ0` using `norm_coeff_of_pow hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b) (2 * j) hlow`. Rewrite `hμ0` using `[← hμdef]`. Establish `ha' : ‖a + μ * (p : K) ^ j‖ ≤ 1`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ hμ0 (norm_nonneg _) hple`. Establish `e1 : rem p f (a + μ * (p : K) ^ j) b = rem p f a b - PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b) * (p : K) ^ j) * g0F K p`. Rewrite using `[← hμdef]`. Unfold `rem`. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `htop1 : PowerSeries.coeff (p ^ (2 * j + 1)) (g0F K p) = ((p : K) ^ (j + 1))⁻¹`. Establish `e : p ^ (2 * j + 1) = p * (p ^ 2) ^ j` using `by ring`. Rewrite using `[e]`. Conclude with `coeff_g0F_of K hp.two_le j`.

Take `⟨-, hlow1⟩` from `correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b) (2 * j) j hlow (g_zero_low_coeff_norm hp hnp j) htop1 e1 (cob_rem_integral hF0 hFl hde hcob ha' b)`. Take `⟨ν, hνdef⟩ : ∃ ν : K, ν = (p : K) * PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (rem p f (a + μ * (p : K) ^ j) b)` from `⟨_, rfl⟩`. Establish `e2 : rem p f (a + μ * (p : K) ^ j) (b + ν * (p : K) ^ j) = rem p f (a + μ * (p : K) ^ j) b - PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (rem p f (a + μ * (p : K) ^ j) b) * (p : K) ^ j) * lgF K p`. Rewrite using `[← hνdef]`. Unfold `rem`.

Rewrite using `[map_add (PowerSeries.C) b]`. Expand and normalize the polynomial expressions, which then agree. Establish `htop2 : PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (lgF K p) = ((p : K) ^ (j + 1))⁻¹`. Establish `e : p ^ (2 * j + 1 + 1) = (p ^ 2) ^ (j + 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `coeff_lgF_pow K hp.two_le (j + 1)`. Take `⟨hν0, hlow2⟩` from `correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha' b) (2 * j + 1) j hlow1 (lg_low hp hnp j) htop2 e2 (cob_rem_integral hF0 hFl hde hcob ha' _)`. Rewrite `hν0` using `[← hνdef]`. Use `⟨a + μ * (p : K) ^ j, b + ν * (p : K) ^ j, ⟨ha', hlow2⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_cancel_left, norm_mul, norm_pow, hnp]`.

Conclude with `mul_le_of_le_one_left (by positivity) hμ0`. Rewrite using `[add_sub_cancel_left, norm_mul, norm_pow, hnp]`. Conclude with `mul_le_of_le_one_left (by positivity) hν0`.
-/
theorem good_succ {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hcob : Integral (cob F f)) (j : ℕ) (a b : K) (hG : Good p f j a b) :
    ∃ a' b' : K, Good p f (j + 1) a' b' ∧ ‖a' - a‖ ≤ ((p : ℝ)⁻¹) ^ j ∧
      ‖b' - b‖ ≤ ((p : ℝ)⁻¹) ^ j := by
  obtain ⟨ha, hlow⟩ := hG
  have hple : ‖(p : K) ^ j‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le

  obtain ⟨μ, hμdef⟩ : ∃ μ : K, μ = (p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b) :=
    ⟨_, rfl⟩
  have hμ0 := norm_coeff_of_pow hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b)
    (2 * j) hlow
  rw [← hμdef] at hμ0
  have ha' : ‖a + μ * (p : K) ^ j‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ?_)
    rw [norm_mul]
    exact mul_le_one₀ hμ0 (norm_nonneg _) hple
  have e1 : rem p f (a + μ * (p : K) ^ j) b = rem p f a b -
      PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b) * (p : K) ^ j) *
        g0F K p := by
    rw [← hμdef]
    unfold rem
    rw [map_add]
    ring
  have htop1 : PowerSeries.coeff (p ^ (2 * j + 1)) (g0F K p) = ((p : K) ^ (j + 1))⁻¹ := by
    have e : p ^ (2 * j + 1) = p * (p ^ 2) ^ j := by ring
    rw [e]
    exact coeff_g0F_of K hp.two_le j
  obtain ⟨-, hlow1⟩ := correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b) (2 * j) j
    hlow (g_zero_low_coeff_norm hp hnp j) htop1 e1 (cob_rem_integral hF0 hFl hde hcob ha' b)

  obtain ⟨ν, hνdef⟩ : ∃ ν : K, ν = (p : K) *
      PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (rem p f (a + μ * (p : K) ^ j) b) := ⟨_, rfl⟩
  have e2 : rem p f (a + μ * (p : K) ^ j) (b + ν * (p : K) ^ j) =
      rem p f (a + μ * (p : K) ^ j) b -
      PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1 + 1))
        (rem p f (a + μ * (p : K) ^ j) b) * (p : K) ^ j) * lgF K p := by
    rw [← hνdef]
    unfold rem
    rw [map_add (PowerSeries.C) b]
    ring
  have htop2 : PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (lgF K p) = ((p : K) ^ (j + 1))⁻¹ := by
    have e : p ^ (2 * j + 1 + 1) = (p ^ 2) ^ (j + 1) := by ring
    rw [e]
    exact coeff_lgF_pow K hp.two_le (j + 1)
  obtain ⟨hν0, hlow2⟩ := correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha' b)
    (2 * j + 1) j hlow1 (lg_low hp hnp j) htop2 e2 (cob_rem_integral hF0 hFl hde hcob ha' _)
  rw [← hνdef] at hν0
  refine ⟨a + μ * (p : K) ^ j, b + ν * (p : K) ^ j, ⟨ha', hlow2⟩, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_mul, norm_pow, hnp]
    exact mul_le_of_le_one_left (by positivity) hμ0
  · rw [add_sub_cancel_left, norm_mul, norm_pow, hnp]
    exact mul_le_of_le_one_left (by positivity) hν0

/- English proof (translation)
Establish `hstep` using `good_succ hp hnp hF0 hFi hF1 hFl hde hcob`. Use `choose! fa fb hfab using hstep`. Take `⟨s, hs0, hs1⟩ : ∃ s : ℕ → K × K, s 0 = (0, PowerSeries.coeff 1 f) ∧ ∀ j, s (j + 1) = (fa j (s j).1 (s j).2, fb j (s j).1 (s j).2)` from `⟨fun j => Nat.rec (0, PowerSeries.coeff 1 f) (fun j t => (fa j t.1 t.2, fb j t.1 t.2)) j, rfl, fun _ => rfl⟩`. Establish `hgood : ∀ j, Good p f j (s j).1 (s j).2`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => rw [hs0]`. Conclude with `good_zero hp hnp hF0 hFi hF1 hFl hde hf0 hcob`. Consider the case `succ j ih => rw [hs1]`. Conclude with `(hfab j _ _ ih).1`.

Establish `hr : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `hca : CauchySeq fun j => (s j).1`. Use `cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, norm_sub_rev, one_mul, hs1]`. Conclude with `(hfab j _ _ (hgood j)).2.1`.

Establish `hcb : CauchySeq fun j => (s j).2`. Use `cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, norm_sub_rev, one_mul, hs1]`. Conclude with `(hfab j _ _ (hgood j)).2.2`. Take `⟨a, hat⟩` from `cauchySeq_tendsto_of_complete hca`.

Take `⟨b, hbt⟩` from `cauchySeq_tendsto_of_complete hcb`. Use `⟨a, b, le_of_tendsto hat.norm (Filter.Eventually.of_forall fun j => (hgood j).1), fun n => ?_⟩` and prove the remaining obligations. Establish `hlim : Filter.Tendsto (fun j => PowerSeries.coeff n (rem p f (s j).1 (s j).2)) Filter.atTop (nhds (PowerSeries.coeff n (rem p f a b)))`. Simplify using `only [coeff_rem]`. Conclude with `(tendsto_const_nhds.sub (hat.mul_const _)).sub (hbt.mul_const _)`.

Use `le_of_tendsto hlim.norm (Filter.eventually_atTop.2 ⟨n, fun j hj => (hgood j).2 n ?_⟩)` and prove the remaining obligations. Establish `: 2 * j + 1 < p ^ (2 * j + 1)` using `Nat.lt_pow_self hp.one_lt`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_limit [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 0) (hcob : Integral (cob F f)) :
    ∃ a b : K, ‖a‖ ≤ 1 ∧ ∀ n, ‖PowerSeries.coeff n (rem p f a b)‖ ≤ 1 := by
  have hstep := good_succ hp hnp hF0 hFi hF1 hFl hde hcob
  choose! fa fb hfab using hstep
  obtain ⟨s, hs0, hs1⟩ : ∃ s : ℕ → K × K, s 0 = (0, PowerSeries.coeff 1 f) ∧
      ∀ j, s (j + 1) = (fa j (s j).1 (s j).2, fb j (s j).1 (s j).2) :=
    ⟨fun j => Nat.rec (0, PowerSeries.coeff 1 f) (fun j t => (fa j t.1 t.2, fb j t.1 t.2)) j,
      rfl, fun _ => rfl⟩
  have hgood : ∀ j, Good p f j (s j).1 (s j).2 := by
    intro j
    induction j with
    | zero => rw [hs0]; exact good_zero hp hnp hF0 hFi hF1 hFl hde hf0 hcob
    | succ j ih => rw [hs1]; exact (hfab j _ _ ih).1
  have hr : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hca : CauchySeq fun j => (s j).1 := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul, hs1]
    exact (hfab j _ _ (hgood j)).2.1
  have hcb : CauchySeq fun j => (s j).2 := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul, hs1]
    exact (hfab j _ _ (hgood j)).2.2
  obtain ⟨a, hat⟩ := cauchySeq_tendsto_of_complete hca
  obtain ⟨b, hbt⟩ := cauchySeq_tendsto_of_complete hcb
  refine ⟨a, b, le_of_tendsto hat.norm (Filter.Eventually.of_forall fun j => (hgood j).1),
    fun n => ?_⟩
  have hlim : Filter.Tendsto (fun j => PowerSeries.coeff n (rem p f (s j).1 (s j).2)) Filter.atTop
      (nhds (PowerSeries.coeff n (rem p f a b))) := by
    simp only [coeff_rem]
    exact (tendsto_const_nhds.sub (hat.mul_const _)).sub (hbt.mul_const _)
  refine le_of_tendsto hlim.norm (Filter.eventually_atTop.2 ⟨n, fun j hj => (hgood j).2 n ?_⟩)
  have : 2 * j + 1 < p ^ (2 * j + 1) := Nat.lt_pow_self hp.one_lt
  omega

end Limit

end LemOne

/- English proof (translation)
Introduce `K _ _ _ _ p σ hU F hF f hf0 hcob`. Take `⟨hp, -, hnp, -, hσ⟩` from `hU`. Establish `hde` using `hDe K p σ hp hnp hσ F hF`. Establish `hF1` using `(hL K p hp hnp F hF).2.2.1`. Take `⟨hF0, hFi, hFl⟩` from `hF`.

Take `⟨a, b, ha, hR⟩` from `LemOne.exists_limit hp hnp hF0 hFi hF1 hFl hde hf0 hcob`. Use `⟨a, b, LemOne.rem p f a b, ha, hR, ?_⟩` and prove the remaining obligations. Unfold `LemOne.rem`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LemmaOne_of (hDe : DeIntegral) (hL : LawSymm) : LemmaOne := by
  intro K _ _ _ _ p σ hU F hF f hf0 hcob
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hde := hDe K p σ hp hnp hσ F hF
  have hF1 := (hL K p hp hnp F hF).2.2.1
  obtain ⟨hF0, hFi, hFl⟩ := hF
  obtain ⟨a, b, ha, hR⟩ := LemOne.exists_limit hp hnp hF0 hFi hF1 hFl hde hf0 hcob
  refine ⟨a, b, LemOne.rem p f a b, ha, hR, ?_⟩
  unfold LemOne.rem
  ring

end Formalism.InvariantFactorPaths.G7
