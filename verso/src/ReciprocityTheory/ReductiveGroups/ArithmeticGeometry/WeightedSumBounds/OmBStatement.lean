import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

namespace ReciprocityTheory.ChartRestriction.G.Sh

open ReciprocityTheory.PGsh

noncomputable section

def OmAStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (lg P : PowerSeries C) (Ω : C),
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      (∀ z : C, z ^ (p ^ 2 - 1) = 1 → PowerSeries.rescale z lg = z • lg) →
      PsIsInt v P → PowerSeries.subst P lg = (p : C) • lg →
      PowerSeries.coeff 0 P = 0 → PowerSeries.coeff 1 P = p →
      (∀ n, 2 ≤ n → n < p ^ 2 → PowerSeries.coeff n P = 0) →
      v (PowerSeries.coeff (p ^ 2) P) = 0 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) → v Ω ≤ ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) →
        v Ω = ((p / ((p : ℝ) ^ 2 - 1) : ℝ) : WithTop ℝ)

def OmBStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 5 ≤ p → v (p : C) = 1 → ∀ (lg P : PowerSeries C) (Ω π : C),
      v π = (((1 : ℝ) / 2 : ℝ) : WithTop ℝ) →
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      (∀ z : C, z ^ (p - 1) = 1 → PowerSeries.rescale z lg = z • lg) →
      PsIsInt v P → PowerSeries.subst P lg = π • lg →
      PowerSeries.coeff 0 P = 0 → PowerSeries.coeff 1 P = π →
      (∀ n, 2 ≤ n → n < p → PowerSeries.coeff n P = 0) →
      v (PowerSeries.coeff p P) = 0 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) → v Ω ≤ ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) →
        v Ω = ((1 / (2 * ((p : ℝ) - 1)) : ℝ) : WithTop ℝ)

def OmCStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (lg : PowerSeries C) (Ω x₁ ζ : C),
      PowerSeries.coeff 0 lg = 0 → PowerSeries.coeff 1 lg = 1 →
      Ω ≠ 0 → PsIsInt v (expComp Ω lg) →
      v x₁ = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) → IsPrimitiveRoot ζ p →
      (∀ N : ℕ, 1 ≤ N → ((N / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) ≤
        v (ζ - ∑ n ∈ Finset.range N, PowerSeries.coeff n (expComp Ω lg) * x₁ ^ n)) →
        v Ω = 0

def OmStatement : Prop := OmAStatement ∧ OmBStatement ∧ OmCStatement

/- English proof (translation)
Establish `hc` using `PowerSeriesCoeffGaps.coeff_subst_gap lg P M hM b hl0 hl1 hlg hP0 hP1 hPg`. Rewrite `hc` using `[hsub, PowerSeries.coeff_smul, smul_eq_mul]`. Establish `hu' : PowerSeries.coeff M P = PowerSeries.coeff M lg * (b + -b ^ M)`. Take the linear combination `-hc`. Establish `hMr : (2 : ℝ) ≤ M` using `by exact_mod_cast hM`.

Establish `hvb : v (-b ^ M) = ((M * β : ℝ) : WithTop ℝ)`. Rewrite using `[v.map_neg, v.map_pow, hb, ← WithTop.coe_nsmul, nsmul_eq_mul]`. Establish `hd : v (b + -b ^ M) = β` using `PowerSeriesCoeffGaps.add_eq_of_lt v hb hvb (by nlinarith)`. Establish `hk0 : PowerSeries.coeff M lg ≠ 0`. Introduce `h0`.

Rewrite `hu` using `[hu', h0, zero_mul, v.map_zero]`. Conclude with `WithTop.top_ne_zero hu`. Take `⟨s, hs⟩` from `PowerSeriesCoeffGaps.exists_real v hk0`. Establish `hs' : s = -β`. Rewrite `hu` using `[hu', v.map_mul, hs, hd, ← WithTop.coe_add]`.

Use `WithTop.coe_eq_zero.mp hu` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI` using `hint M`. Unfold `IsIntV at hI`. Rewrite `hI` using `[PowerSeriesCoeffGaps.coeff_expComp_gap Ω lg M hM hl0 hl1 hlg]`.

Establish `hx : v (Ω * PowerSeries.coeff M lg) = ((r + -β : ℝ) : WithTop ℝ)`. Rewrite using `[v.map_mul, hr, hs, hs', WithTop.coe_add]`. Establish `hy : v (Ω ^ M / (M.factorial : C)) = ((M * r - φ : ℝ) : WithTop ℝ)` using `PowerSeriesCoeffGaps.div_eq_coe v (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)) (by rw [v.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]) hfac`. Use `PowerSeriesCoeffGaps.eq_of_nonneg_add v (by linarith) hx hy hI` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem key {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (lg P : PowerSeries C) (Ω b : C) (M : ℕ) (hM : 2 ≤ M) (β φ r : ℝ) (hβ : 0 < β)
    (hb : v b = β) (hfac : v (M.factorial : C) = φ) (hr : v Ω = r) (hrβ : r < β)
    (hl0 : PowerSeries.coeff 0 lg = 0) (hl1 : PowerSeries.coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j lg = 0)
    (hsub : PowerSeries.subst P lg = b • lg) (hP0 : PowerSeries.coeff 0 P = 0)
    (hP1 : PowerSeries.coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j P = 0)
    (hu : v (PowerSeries.coeff M P) = 0) (hint : PsIsInt v (expComp Ω lg)) :
    r - β = M * r - φ := by
  have hc := PowerSeriesCoeffGaps.coeff_subst_gap lg P M hM b hl0 hl1 hlg hP0 hP1 hPg
  rw [hsub, PowerSeries.coeff_smul, smul_eq_mul] at hc
  have hu' : PowerSeries.coeff M P = PowerSeries.coeff M lg * (b + -b ^ M) := by
    linear_combination -hc
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hvb : v (-b ^ M) = ((M * β : ℝ) : WithTop ℝ) := by
    rw [v.map_neg, v.map_pow, hb, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hd : v (b + -b ^ M) = β := PowerSeriesCoeffGaps.add_eq_of_lt v hb hvb (by nlinarith)
  have hk0 : PowerSeries.coeff M lg ≠ 0 := by
    intro h0
    rw [hu', h0, zero_mul, v.map_zero] at hu
    exact WithTop.top_ne_zero hu
  obtain ⟨s, hs⟩ := PowerSeriesCoeffGaps.exists_real v hk0
  have hs' : s = -β := by
    rw [hu', v.map_mul, hs, hd, ← WithTop.coe_add] at hu
    have := WithTop.coe_eq_zero.mp hu
    linarith
  have hI := hint M
  unfold IsIntV at hI
  rw [PowerSeriesCoeffGaps.coeff_expComp_gap Ω lg M hM hl0 hl1 hlg] at hI
  have hx : v (Ω * PowerSeries.coeff M lg) = ((r + -β : ℝ) : WithTop ℝ) := by
    rw [v.map_mul, hr, hs, hs', WithTop.coe_add]
  have hy : v (Ω ^ M / (M.factorial : C)) = ((M * r - φ : ℝ) : WithTop ℝ) :=
    PowerSeriesCoeffGaps.div_eq_coe v (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M))
      (by rw [v.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]) hfac
  have := PowerSeriesCoeffGaps.eq_of_nonneg_add v (by linarith) hx hy hI
  linarith

/- English proof (translation)
Introduce `C _ _ _ v p hp hp3 hp1 lg P Ω hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle`. Establish `hM : 2 ≤ p ^ 2` using `le_trans (by omega) (Nat.le_self_pow (by norm_num) p)`. Establish `hp1' : v (p : C) = ((1 : ℝ) : WithTop ℝ)` using `by rw [hp1, WithTop.coe_one]`. Take `⟨r, hr⟩` from `PowerSeriesCoeffGaps.exists_real v hΩ`. Establish `hpR : (3 : ℝ) ≤ p` using `by exact_mod_cast hp3`.

Establish `hrle : r ≤ 1 / ((p : ℝ) - 1)` using `by rw [hr] at hle; exact_mod_cast hle`. Establish `hlt1 : 1 / ((p : ℝ) - 1) < 1` using `(div_lt_one (by linarith)).mpr (by linarith)`. Establish `hfac : v (((p ^ 2).factorial : ℕ) : C) = (((p + 1 : ℕ) : ℝ) : WithTop ℝ)`. Rewrite using `[PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _), PowerSeriesCoeffGaps.factorization_factorial_sq hp]`. Establish `e` using `key v lg P Ω (p : C) (p ^ 2) hM 1 ((p + 1 : ℕ) : ℝ) r one_pos hp1' hfac hr (by linarith) hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg (p ^ 2) hM hsym) hsub hP0 hP1 hPg hu hint`.

Rewrite using `[hr]`. Use `congr 1`. Move the coercions through the operations in `at e`. Rewrite using `[eq_div_iff (ne_of_gt (by nlinarith))]`. Take the linear combination `-e`.
-/
theorem omA : OmAStatement := by
  intro C _ _ _ v p hp hp3 hp1 lg P Ω hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle
  have hM : 2 ≤ p ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) p)
  have hp1' : v (p : C) = ((1 : ℝ) : WithTop ℝ) := by rw [hp1, WithTop.coe_one]
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hrle : r ≤ 1 / ((p : ℝ) - 1) := by rw [hr] at hle; exact_mod_cast hle
  have hlt1 : 1 / ((p : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hfac : v (((p ^ 2).factorial : ℕ) : C) = (((p + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _),
      PowerSeriesCoeffGaps.factorization_factorial_sq hp]
  have e := key v lg P Ω (p : C) (p ^ 2) hM 1 ((p + 1 : ℕ) : ℝ) r one_pos hp1' hfac hr
    (by linarith) hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg (p ^ 2) hM hsym) hsub hP0 hP1 hPg hu hint
  rw [hr]
  congr 1
  push_cast at e
  rw [eq_div_iff (ne_of_gt (by nlinarith))]
  linear_combination -e

/- English proof (translation)
Introduce `C _ _ _ v p hp hp5 hp1 lg P Ω π hπ hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle`. Establish `hM : 2 ≤ p` using `hp.two_le`. Take `⟨r, hr⟩` from `PowerSeriesCoeffGaps.exists_real v hΩ`. Establish `hpR : (5 : ℝ) ≤ p` using `by exact_mod_cast hp5`. Establish `hrle : r ≤ 1 / ((p : ℝ) - 1)` using `by rw [hr] at hle; exact_mod_cast hle`.

Establish `hlt : 1 / ((p : ℝ) - 1) < 1 / 2`. Rewrite using `[div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith`. Establish `hfac : v ((p.factorial : ℕ) : C) = (((1 : ℕ) : ℝ) : WithTop ℝ)`. Rewrite using `[PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _), PowerSeriesCoeffGaps.factorization_factorial_self hp]`. Establish `e` using `key v lg P Ω π p hM (1 / 2) ((1 : ℕ) : ℝ) r (by norm_num) hπ hfac hr (by linarith) hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg p hM hsym) hsub hP0 hP1 hPg hu hint`.

Rewrite using `[hr]`. Use `congr 1`. Move the coercions through the operations in `at e`. Rewrite using `[eq_div_iff (ne_of_gt (by linarith))]`. Take the linear combination `-2 * e`.
-/
theorem omB : OmBStatement := by
  intro C _ _ _ v p hp hp5 hp1 lg P Ω π hπ hl0 hl1 hsym _ hsub hP0 hP1 hPg hu hΩ hint hle
  have hM : 2 ≤ p := hp.two_le
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hrle : r ≤ 1 / ((p : ℝ) - 1) := by rw [hr] at hle; exact_mod_cast hle
  have hlt : 1 / ((p : ℝ) - 1) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hfac : v ((p.factorial : ℕ) : C) = (((1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [PowerSeriesCoeffGaps.natCast_eq_factorization v hp hp1 (Nat.factorial_ne_zero _),
      PowerSeriesCoeffGaps.factorization_factorial_self hp]
  have e := key v lg P Ω π p hM (1 / 2) ((1 : ℕ) : ℝ) r (by norm_num) hπ hfac hr (by linarith)
    hl0 hl1 (PowerSeriesCoeffGaps.coeff_eq_zero_of_symm lg p hM hsym) hsub hP0 hP1 hPg hu hint
  rw [hr]
  congr 1
  push_cast at e
  rw [eq_div_iff (ne_of_gt (by linarith))]
  linear_combination -2 * e

/- English proof (translation)
Introduce `C _ _ _ v p hp hp1 lg Ω x₁ ζ hl0 hl1 hΩ _ hx hζ hN`. Establish `h2` using `hN 2 (by norm_num)`. Establish `hc0 : PowerSeries.coeff 0 (expComp Ω lg) = 1`. Simplify using `[expComp, PowerSeries.coeff_mk]`. Establish `hc1 : PowerSeries.coeff 1 (expComp Ω lg) = Ω`.

Rewrite using `[expComp, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]`. Simplify using `[hl1]`. Rewrite `h2` using `[Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, pow_zero, pow_one, mul_one]`. Establish `hz` using `PowerSeriesCoeffGaps.v_zeta_sub_one v hp hp1 hζ`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`.

Establish `hlt : ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) < v (ζ - (1 + Ω * x₁))`. Use `lt_of_lt_of_le ?_ h2` and prove the remaining obligations. Establish `h12 : 1 / ((p : ℝ) - 1) < ((2 : ℕ) : ℝ) / ((p : ℝ) - 1)`. Rewrite using `[div_lt_div_iff_of_pos_right (by linarith)]; norm_num`. Conclude with `WithTop.coe_lt_coe.mpr h12`.

Establish `e : Ω * x₁ = (ζ - 1) + -(ζ - (1 + Ω * x₁))` using `by ring`. Establish `hd : v (ζ - 1) ≠ v (-(ζ - (1 + Ω * x₁)))` using `by rw [v.map_neg, hz]; exact hlt.ne`. Establish `hv : v (Ω * x₁) = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ)`. Rewrite using `[e, v.map_add_of_distinct_val hd, hz, v.map_neg, min_eq_left hlt.le]`. Take `⟨r, hr⟩` from `PowerSeriesCoeffGaps.exists_real v hΩ`.

Rewrite `hv` using `[v.map_mul, hr, hx, ← WithTop.coe_add]`. Establish `h3` using `WithTop.coe_injective hv`. Establish `h4 : r = 0` using `by linarith`. Rewrite using `[hr, h4, WithTop.coe_zero]`.
-/
theorem omC : OmCStatement := by
  intro C _ _ _ v p hp hp1 lg Ω x₁ ζ hl0 hl1 hΩ _ hx hζ hN
  have h2 := hN 2 (by norm_num)
  have hc0 : PowerSeries.coeff 0 (expComp Ω lg) = 1 := by
    simp [expComp, PowerSeries.coeff_mk]
  have hc1 : PowerSeries.coeff 1 (expComp Ω lg) = Ω := by
    rw [expComp, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hl1]
  rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, pow_zero, pow_one, mul_one] at h2
  have hz := PowerSeriesCoeffGaps.v_zeta_sub_one v hp hp1 hζ
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlt : ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) < v (ζ - (1 + Ω * x₁)) := by
    refine lt_of_lt_of_le ?_ h2
    have h12 : 1 / ((p : ℝ) - 1) < ((2 : ℕ) : ℝ) / ((p : ℝ) - 1) := by
      rw [div_lt_div_iff_of_pos_right (by linarith)]; norm_num
    exact WithTop.coe_lt_coe.mpr h12
  have e : Ω * x₁ = (ζ - 1) + -(ζ - (1 + Ω * x₁)) := by ring
  have hd : v (ζ - 1) ≠ v (-(ζ - (1 + Ω * x₁))) := by rw [v.map_neg, hz]; exact hlt.ne
  have hv : v (Ω * x₁) = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) := by
    rw [e, v.map_add_of_distinct_val hd, hz, v.map_neg, min_eq_left hlt.le]
  obtain ⟨r, hr⟩ := PowerSeriesCoeffGaps.exists_real v hΩ
  rw [v.map_mul, hr, hx, ← WithTop.coe_add] at hv
  have h3 := WithTop.coe_injective hv
  have h4 : r = 0 := by linarith
  rw [hr, h4, WithTop.coe_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨omA, omB, omC⟩`.
-/
theorem om : OmStatement := ⟨omA, omB, omC⟩

end

end ReciprocityTheory.ChartRestriction.G.Sh
