import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthRadii

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}

/- English proof (translation)
Introduce `α`. Use `le_trans (WithTop.coe_le_coe.mpr ?_) (h α)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ordGe_mono {g : MvPowerSeries (Fin M) C} {r s : ℝ} (h : OrdGe v ρ g r) (hs : s ≤ r) :
    OrdGe v ρ g s := by
  intro α
  refine le_trans (WithTop.coe_le_coe.mpr ?_) (h α)
  linarith

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem ordGe_one : OrdGe v ρ (1 : MvPowerSeries (Fin M) C) 0 := by
  intro α
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPowerSeries.coeff_mul]`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce and unpack `⟨β, γ⟩ hβγ`. Rewrite `hβγ` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[AddValuation.map_mul]`. Establish `e : r + s - ∑ m, ρ m * ((α m : ℕ) : ℝ) = (r - ∑ m, ρ m * ((β m : ℕ) : ℝ)) + (s - ∑ m, ρ m * ((γ m : ℕ) : ℝ))`. Rewrite using `[← hβγ]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, WithTop.coe_add]`. Conclude with `add_le_add (hg β) (hh γ)`.
-/
theorem ordGe_mul {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg : OrdGe v ρ g r)
    (hh : OrdGe v ρ h s) : OrdGe v ρ (g * h) (r + s) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  apply AddValuation.map_le_sum
  rintro ⟨β, γ⟩ hβγ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
  rw [AddValuation.map_mul]
  have e : r + s - ∑ m, ρ m * ((α m : ℕ) : ℝ) =
      (r - ∑ m, ρ m * ((β m : ℕ) : ℝ)) + (s - ∑ m, ρ m * ((γ m : ℕ) : ℝ)) := by
    rw [← hβγ]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hg β) (hh γ)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => rw [pow_zero, Nat.cast_zero, zero_mul]`. Conclude with `ordGe_one`. Consider the case `succ N ih`. Rewrite using `[pow_succ]`.

Establish `e : ((N + 1 : ℕ) : ℝ) * r = (N : ℝ) * r + r` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `ordGe_mul ih hg`.
-/
theorem ordGe_pow {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg : OrdGe v ρ g r) (N : ℕ) :
    OrdGe v ρ (g ^ N) ((N : ℝ) * r) := by
  induction N with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact ordGe_one
  | succ N ih =>
    rw [pow_succ]
    have e : ((N + 1 : ℕ) : ℝ) * r = (N : ℝ) * r + r := by push_cast; ring
    rw [e]
    exact ordGe_mul ih hg

def Agree (D : ℕ) (g g' : MvPowerSeries (Fin M) C) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D → coeff α g = coeff α g'

/- English proof (translation)
Introduce `α hα` and use `h α (lt_of_lt_of_le hα hD)`.
-/
theorem agree_mono {D D' : ℕ} {g g' : MvPowerSeries (Fin M) C} (h : Agree D g g') (hD : D' ≤ D) :
    Agree D' g g' := fun α hα => h α (lt_of_lt_of_le hα hD)

/- English proof (translation)
Introduce `α hα`. Rewrite using `[MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce and unpack `⟨β, γ⟩ hβγ`. Rewrite `hβγ` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Simplify using `only`. Establish `hdeg : Finsupp.degree β + Finsupp.degree γ = Finsupp.degree α`. Rewrite using `[← hβγ, map_add]`. Distinguish the cases in `hβ : β = 0`. Substitute `hβ` using the available equality.

Simplify using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', zero_mul]`. Distinguish the cases in `hγ : γ = 0`. Substitute `hγ` using the available equality. Simplify using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, hh0', mul_zero]`. Establish `hβd : Finsupp.degree β ≠ 0` using `fun h0 => hβ ((Finsupp.degree_eq_zero_iff β).mp h0)`.

Establish `hγd : Finsupp.degree γ ≠ 0` using `fun h0 => hγ ((Finsupp.degree_eq_zero_iff γ).mp h0)`. Rewrite using `[hg β (by omega), hh γ (by omega)]`.
-/
theorem agree_mul {D : ℕ} {g g' h h' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hh0 : constantCoeff h = 0) (hh0' : constantCoeff h' = 0)
    (hg : Agree D g g') (hh : Agree D h h') : Agree (D + 1) (g * h) (g' * h') := by
  intro α hα
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨β, γ⟩ hβγ
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
  dsimp only
  have hdeg : Finsupp.degree β + Finsupp.degree γ = Finsupp.degree α := by
    rw [← hβγ, map_add]
  by_cases hβ : β = 0
  · subst hβ
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', zero_mul]
  by_cases hγ : γ = 0
  · subst hγ
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, hh0', mul_zero]

  have hβd : Finsupp.degree β ≠ 0 := fun h0 => hβ ((Finsupp.degree_eq_zero_iff β).mp h0)
  have hγd : Finsupp.degree γ ≠ 0 := fun h0 => hγ ((Finsupp.degree_eq_zero_iff γ).mp h0)
  rw [hg β (by omega), hh γ (by omega)]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hg`. Consider the case `succ k ih`. Rewrite using `[pow_succ g (k + 1), pow_succ g' (k + 1)]`. Use `agree_mono (agree_mul ?_ ?_ hg0 hg0' ih hg) (Nat.le_succ D)` and prove the remaining obligations.

Rewrite using `[map_pow, hg0, zero_pow (Nat.succ_ne_zero k)]`. Rewrite using `[map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]`.
-/
theorem agree_pow_succ {D : ℕ} {g g' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hg : Agree D g g') (k : ℕ) :
    Agree D (g ^ (k + 1)) (g' ^ (k + 1)) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [pow_succ g (k + 1), pow_succ g' (k + 1)]
    refine agree_mono (agree_mul ?_ ?_ hg0 hg0' ih hg) (Nat.le_succ D)
    · rw [map_pow, hg0, zero_pow (Nat.succ_ne_zero k)]
    · rw [map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, N = k + 1 + 1` from `⟨N - 2, by omega⟩`. Rewrite using `[pow_succ g (k + 1), pow_succ g' (k + 1)]`. Conclude with `agree_mul (by rw [map_pow, hg0, zero_pow (Nat.succ_ne_zero k)]) (by rw [map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]) hg0 hg0' (agree_pow_succ hg0 hg0' hg k) hg`.
-/
theorem agree_pow {D : ℕ} {g g' : MvPowerSeries (Fin M) C} (hg0 : constantCoeff g = 0)
    (hg0' : constantCoeff g' = 0) (hg : Agree D g g') {N : ℕ} (hN : 2 ≤ N) :
    Agree (D + 1) (g ^ N) (g' ^ N) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [pow_succ g (k + 1), pow_succ g' (k + 1)]
  exact agree_mul (by rw [map_pow, hg0, zero_pow (Nat.succ_ne_zero k)])
    (by rw [map_pow, hg0', zero_pow (Nat.succ_ne_zero k)]) hg0 hg0' (agree_pow_succ hg0 hg0' hg k) hg

end

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Unfold `radius`. Establish `h1 : -(2 * (-1 : ℤ) + 1) = 1` using `by norm_num`. Rewrite using `[h1, zpow_one]`. Establish `h2 : (p : ℝ) - 1 ≠ 0` using `by linarith`.

Establish `h3 : (p : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Rewrite using `[div_eq_div_iff h3 h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radius_neg_one {p : ℕ} (hp : 3 ≤ p) : radius p (-1) = 1 / ((p : ℝ) - 1) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have h1 : -(2 * (-1 : ℤ) + 1) = 1 := by norm_num
  rw [h1, zpow_one]
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [div_eq_div_iff h3 h2]
  ring

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Unfold `radius`. Establish `hden : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `: (p : ℝ) ^ (-(2 * k + 1)) ≤ (p : ℝ) ^ (-(2 * j + 1))` using `zpow_le_zpow_right₀ (by linarith) (by omega)`. Conclude with `div_le_div_of_nonneg_right (by linarith) hden.le`.
-/
theorem radius_anti {p : ℕ} (hp : 3 ≤ p) {j k : ℤ} (h : j ≤ k) : radius p k ≤ radius p j := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have : (p : ℝ) ^ (-(2 * k + 1)) ≤ (p : ℝ) ^ (-(2 * j + 1)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/- English proof (translation)
Rewrite using `[← radius_neg_one hp]`. Conclude with `radius_anti hp h`.
-/
theorem radius_le_top {p : ℕ} (hp : 3 ≤ p) {k : ℤ} (h : -1 ≤ k) : radius p k ≤ 1 / ((p : ℝ) - 1) := by
  rw [← radius_neg_one hp]
  exact radius_anti hp h

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Unfold `radius`. Establish `hden : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `: 0 < (p : ℝ) ^ (-(2 * k + 1))` using `zpow_pos (by linarith) _`. Conclude with `div_le_div_of_nonneg_right (by linarith) hden.le`.
-/
theorem radius_ge {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 1 / ((p : ℝ) ^ 2 - 1) ≤ radius p k := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have : 0 < (p : ℝ) ^ (-(2 * k + 1)) := zpow_pos (by linarith) _
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hden : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Conclude with `le_trans (div_nonneg zero_le_one hden.le) (radius_ge hp k)`.
-/
theorem radius_pos {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : 0 ≤ radius p k := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  exact le_trans (div_nonneg zero_le_one hden.le) (radius_ge hp k)

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Unfold `radius`. Establish `hden : (p : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Establish `hp0 : (p : ℝ) ≠ 0` using `by linarith`. Establish `e : (p : ℝ) ^ (-(2 * (k - 1) + 1)) = (p : ℝ) ^ 2 * (p : ℝ) ^ (-(2 * k + 1))`.

Rewrite using `[show -(2 * (k - 1) + 1) = (2 : ℤ) + -(2 * k + 1) by ring, zpow_add₀ hp0, zpow_two, sq]`. Rewrite using `[e, mul_div_assoc', div_sub_one hden]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radius_rec {p : ℕ} (hp : 3 ≤ p) (k : ℤ) : (p : ℝ) ^ 2 * radius p k - 1 = radius p (k - 1) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold radius
  have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have e : (p : ℝ) ^ (-(2 * (k - 1) + 1)) = (p : ℝ) ^ 2 * (p : ℝ) ^ (-(2 * k + 1)) := by
    rw [show -(2 * (k - 1) + 1) = (2 : ℤ) + -(2 * k + 1) by ring, zpow_add₀ hp0, zpow_two, sq]
  rw [e, mul_div_assoc', div_sub_one hden]
  congr 1
  ring

/- English proof (translation)
Establish `h0 : (0 : ℝ) ≤ p - 3` using `by linarith`. Establish `h1 : p + 1 ≤ p ^ 3` using `by nlinarith [mul_nonneg (sq_nonneg p) h0, sq_nonneg p]`. Proceed by induction on `m with`. Consider the case `zero`. Simplify using `only [Nat.cast_zero, zero_add]`.

Use polynomial arithmetic with `[mul_nonneg (sq_nonneg p) h0, mul_nonneg (by linarith : (0 : ℝ) ≤ p) (by linarith : (0 : ℝ) ≤ p - 1)]`. Consider the case `succ m ih`. Establish `h3 : p ^ 3 ≤ p ^ (m + 3)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Rewrite using `[show m + 1 + 3 = (m + 3) + 1 by ring, pow_succ p (m + 3)]`. Use `push_cast`.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ p ^ (m + 3) - (p + 1))]`.
-/
theorem big_pow {p : ℝ} (hp : 3 ≤ p) (m : ℕ) :
    (p + 1) + ((m : ℝ) + 2) * (p ^ 2 - 1) ≤ p ^ (m + 3) := by
  have h0 : (0 : ℝ) ≤ p - 3 := by linarith
  have h1 : p + 1 ≤ p ^ 3 := by nlinarith [mul_nonneg (sq_nonneg p) h0, sq_nonneg p]
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    nlinarith [mul_nonneg (sq_nonneg p) h0, mul_nonneg (by linarith : (0 : ℝ) ≤ p)
      (by linarith : (0 : ℝ) ≤ p - 1)]
  | succ m ih =>
    have h3 : p ^ 3 ≤ p ^ (m + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [show m + 1 + 3 = (m + 3) + 1 by ring, pow_succ p (m + 3)]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ p ^ (m + 3) - (p + 1))]

/- English proof (translation)
Establish `hp' : (3 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hpm : 0 < (p : ℝ) - 1` using `by linarith`. Establish `hQ : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Break down `lt_or_ge (dp a) 0 with ha | ha` into its components or cases. Establish `ha' : dp a = -1` using `by have := hdp a; omega`.

Use `le_trans (WithTop.coe_le_coe.mpr ?_) (hc a n b)` and prove the remaining obligations. Rewrite using `[ha', radius_neg_one hp]`. Establish `hb` using `radius_le_top hp (hdp b)`. Use `set w := 1 / ((p : ℝ) - 1) with hwdef`. Establish `hw : ((p : ℝ) - 1) * w = 1` using `mul_one_div_cancel hpm.ne'`.

Establish `hw0 : 0 < w` using `one_div_pos.mpr hpm`. Establish `hbern : 1 + (n : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ n`. Use `one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) - 1 by linarith) n` as an intermediate fact. Simplify using `using this`. Establish `hprod` using `mul_nonneg (sub_nonneg.mpr hbern) hw0.le`.

Establish `hnw : (n : ℝ) * (((p : ℝ) - 1) * w) = n` using `by rw [hw, mul_one]`. Use polynomial arithmetic with `[hprod, hnw, hb]`. Take `⟨hc1, hcn, hc2⟩` from `hgood a ha`. Use `le_trans (WithTop.coe_le_coe.mpr ?_) (hcn n b hn)` and prove the remaining obligations. Break down `(show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3` into its components or cases.

Substitute `h1` using the available equality. Conclude with `absurd (show c a 1 b = 0 by rw [hc1]; rfl) hne`. Substitute `h2` using the available equality. Establish `hb : dp a - 1 ≤ dp b` using `hc2 b hne`. Use `radius_anti hp hb` as an intermediate fact.

Rewrite `this` using `[← radius_rec hp]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, rfl⟩ : ∃ m, n = m + 3` from `⟨n - 3, by omega⟩`. Establish `hb` using `radius_le_top hp (hdp b)`.

Establish `hge` using `radius_ge hp (dp a)`. Establish `hbig` using `big_pow hp' m`. Use `set u := 1 / ((p : ℝ) ^ 2 - 1) with hudef`. Establish `hu : ((p : ℝ) ^ 2 - 1) * u = 1` using `mul_one_div_cancel hQ.ne'`. Establish `hu0 : 0 < u` using `one_div_pos.mpr hQ`.

Establish `hC : 1 / ((p : ℝ) - 1) = ((p : ℝ) + 1) * u`. Rewrite using `[hudef, mul_one_div, div_eq_div_iff hpm.ne' hQ.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hA` using `mul_le_mul_of_nonneg_right hbig hu0.le`. Establish `hB` using `mul_le_mul_of_nonneg_left hge (pow_nonneg (by linarith : (0 : ℝ) ≤ p) (m + 3))`.

Establish `hu' : ((m : ℝ) + 2) * (((p : ℝ) ^ 2 - 1) * u) = (m : ℝ) + 2` using `by rw [hu, mul_one]`. Use `push_cast`. Use polynomial arithmetic with `[hA, hB, hb, hC, hu']`.
-/
theorem term_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : 3 ≤ p)
    {d : ℕ} (dp : Fin d → ℤ) (c : Fin d → ℕ → Fin d → C) (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    (a : Fin d) (n : ℕ) (b : Fin d) (hn : 1 ≤ n) (hne : c a n b ≠ 0) :
    ((radius p (dp b) - (p : ℝ) ^ n * radius p (dp a) : ℝ) : WithTop ℝ) ≤ v (c a n b) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hQ : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  rcases lt_or_ge (dp a) 0 with ha | ha
  ·
    have ha' : dp a = -1 := by have := hdp a; omega
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hc a n b)
    rw [ha', radius_neg_one hp]
    have hb := radius_le_top hp (hdp b)
    set w := 1 / ((p : ℝ) - 1) with hwdef
    have hw : ((p : ℝ) - 1) * w = 1 := mul_one_div_cancel hpm.ne'
    have hw0 : 0 < w := one_div_pos.mpr hpm
    have hbern : 1 + (n : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ n := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) - 1 by linarith) n
      simpa using this
    have hprod := mul_nonneg (sub_nonneg.mpr hbern) hw0.le
    have hnw : (n : ℝ) * (((p : ℝ) - 1) * w) = n := by rw [hw, mul_one]
    nlinarith [hprod, hnw, hb]
  · obtain ⟨hc1, hcn, hc2⟩ := hgood a ha
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hcn n b hn)
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · subst h1
      exact absurd (show c a 1 b = 0 by rw [hc1]; rfl) hne
    ·
      subst h2
      have hb : dp a - 1 ≤ dp b := hc2 b hne
      have := radius_anti hp hb
      rw [← radius_rec hp] at this
      push_cast
      linarith
    ·
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hb := radius_le_top hp (hdp b)
      have hge := radius_ge hp (dp a)
      have hbig := big_pow hp' m
      set u := 1 / ((p : ℝ) ^ 2 - 1) with hudef
      have hu : ((p : ℝ) ^ 2 - 1) * u = 1 := mul_one_div_cancel hQ.ne'
      have hu0 : 0 < u := one_div_pos.mpr hQ
      have hC : 1 / ((p : ℝ) - 1) = ((p : ℝ) + 1) * u := by
        rw [hudef, mul_one_div, div_eq_div_iff hpm.ne' hQ.ne']
        ring
      have hA := mul_le_mul_of_nonneg_right hbig hu0.le
      have hB := mul_le_mul_of_nonneg_left hge (pow_nonneg (by linarith : (0 : ℝ) ≤ p) (m + 3))
      have hu' : ((m : ℝ) + 2) * (((p : ℝ) ^ 2 - 1) * u) = (m : ℝ) + 2 := by rw [hu, mul_one]
      push_cast
      nlinarith [hA, hB, hb, hC, hu']

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

noncomputable section

variable {C : Type} [Field C] {d M : ℕ}

def Phi (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z t : Fin d → MvPowerSeries (Fin M) C) :
    Fin d → MvPowerSeries (Fin M) C :=
  fun b => z b - lgSum p c t b + t b

/- English proof (translation)
Establish `hl : coeff α (lgSum p c t b) = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n))` using `rfl`. Establish `h0 : ∑ a, c a 0 b * coeff α (t a ^ (p ^ 0)) = coeff α (t b)`. Simplify using `only [hc0, pow_zero, pow_one, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `only [Phi, map_add, map_sub, hl, Finset.sum_range_succ', h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_Phi {p : ℕ} {c : Fin d → ℕ → Fin d → C} (hc0 : ∀ a, c a 0 = Pi.single a 1)
    (z t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) (α : Fin M →₀ ℕ) :
    coeff α (Phi p c z t b) = coeff α (z b) - ∑ n ∈ Finset.range (Finsupp.degree α),
      ∑ a, c a (n + 1) b * coeff α (t a ^ (p ^ (n + 1))) := by
  have hl : coeff α (lgSum p c t b) = ∑ n ∈ Finset.range (Finsupp.degree α + 1),
      ∑ a, c a n b * coeff α (t a ^ (p ^ n)) := rfl
  have h0 : ∑ a, c a 0 b * coeff α (t a ^ (p ^ 0)) = coeff α (t b) := by
    simp only [hc0, pow_zero, pow_one, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Phi, map_add, map_sub, hl, Finset.sum_range_succ', h0]
  ring

def iterT (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z : Fin d → MvPowerSeries (Fin M) C) :
    ℕ → Fin d → MvPowerSeries (Fin M) C :=
  fun k => Nat.rec (motive := fun _ => Fin d → MvPowerSeries (Fin M) C) 0
    (fun _ t => Phi p c z t) k

def limT (p : ℕ) (c : Fin d → ℕ → Fin d → C) (z : Fin d → MvPowerSeries (Fin M) C) :
    Fin d → MvPowerSeries (Fin M) C :=
  fun b α => coeff α (iterT p c z (Finsupp.degree α + 1) b)

section
variable {p : ℕ} {c : Fin d → ℕ → Fin d → C} {z : Fin d → MvPowerSeries (Fin M) C}
  (hp : 3 ≤ p) (hc0 : ∀ a, c a 0 = Pi.single a 1)
  (hz : ∀ b (α : Fin M →₀ ℕ), Finsupp.degree α ≠ 1 → coeff α (z b) = 0)
include hc0 hz

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Phi hc0]`. Simplify using `only [map_zero, Finset.range_zero, Finset.sum_empty, sub_zero]`. Conclude with `hz b 0 (by simp)`.
-/
theorem const_Phi (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) :
    constantCoeff (Phi p c z t b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Phi hc0]
  simp only [map_zero, Finset.range_zero, Finset.sum_empty, sub_zero]
  exact hz b 0 (by simp)

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => show constantCoeff (0 : MvPowerSeries (Fin M) C) = 0`. Conclude with `map_zero _`. Consider the case `succ k => exact const_Phi hc0 hz _ b`.
-/
theorem const_iterT (k : ℕ) (b : Fin d) : constantCoeff (iterT p c z k b) = 0 := by
  cases k with
  | zero => show constantCoeff (0 : MvPowerSeries (Fin M) C) = 0; exact map_zero _
  | succ k => exact const_Phi hc0 hz _ b

include hp

/- English proof (translation)
Introduce `α hα`. Rewrite using `[coeff_Phi hc0, coeff_Phi hc0]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Establish `hN : 2 ≤ p ^ (n + 1)` using `le_trans (by omega) (le_self_pow (by omega) (Nat.succ_ne_zero n))`. Rewrite using `[agree_pow (hs a) (hs' a) (h a) hN α hα]`.
-/
theorem agree_Phi {D : ℕ} {s s' : Fin d → MvPowerSeries (Fin M) C}
    (hs : ∀ b, constantCoeff (s b) = 0) (hs' : ∀ b, constantCoeff (s' b) = 0)
    (h : ∀ b, Agree D (s b) (s' b)) (b : Fin d) :
    Agree (D + 1) (Phi p c z s b) (Phi p c z s' b) := by
  intro α hα
  rw [coeff_Phi hc0, coeff_Phi hc0]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro a _
  have hN : 2 ≤ p ^ (n + 1) := le_trans (by omega) (le_self_pow (by omega) (Nat.succ_ne_zero n))
  rw [agree_pow (hs a) (hs' a) (h a) hN α hα]

/- English proof (translation)
Proceed by induction on `k generalizing b with`. Consider the case `zero => intro α hα`. Conclude with `absurd hα (Nat.not_lt_zero _)`. Consider the case `succ k ih`. Conclude with `agree_Phi hp hc0 hz (const_iterT hc0 hz k) (const_iterT hc0 hz (k + 1)) ih b`.
-/
theorem agree_iterT (k : ℕ) (b : Fin d) :
    Agree k (iterT p c z k b) (iterT p c z (k + 1) b) := by
  induction k generalizing b with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ k ih =>
    exact agree_Phi hp hc0 hz (const_iterT hc0 hz k) (const_iterT hc0 hz (k + 1)) ih b

/- English proof (translation)
Proceed by induction on `m, hkm using Nat.le_induction with`. Consider the case `base => intro α _`. Both sides reduce to the same expression. Consider the case `succ m hkm ih`. Introduce `α hα`.

Rewrite using `[ih α hα]`. Conclude with `agree_iterT hp hc0 hz m b α (lt_of_lt_of_le hα hkm)`.
-/
theorem agree_iterT_le (k m : ℕ) (hkm : k ≤ m) (b : Fin d) :
    Agree k (iterT p c z k b) (iterT p c z m b) := by
  induction m, hkm using Nat.le_induction with
  | base => intro α _; rfl
  | succ m hkm ih =>
    intro α hα
    rw [ih α hα]
    exact agree_iterT hp hc0 hz m b α (lt_of_lt_of_le hα hkm)

/- English proof (translation)
Introduce `α hα`. Use `show coeff α (iterT p c z (Finsupp.degree α + 1) b) = coeff α (iterT p c z K b)`. Conclude with `agree_iterT_le hp hc0 hz _ _ (by omega) b α (Nat.lt_succ_self _)`.
-/
theorem agree_limT (K : ℕ) (b : Fin d) : Agree K (limT p c z b) (iterT p c z K b) := by
  intro α hα
  show coeff α (iterT p c z (Finsupp.degree α + 1) b) = coeff α (iterT p c z K b)
  exact agree_iterT_le hp hc0 hz _ _ (by omega) b α (Nat.lt_succ_self _)

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Use `show coeff 0 (iterT p c z (Finsupp.degree (0 : Fin M →₀ ℕ) + 1) b) = 0`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `const_iterT hc0 hz _ b`.
-/
theorem const_limT (b : Fin d) : constantCoeff (limT p c z b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show coeff 0 (iterT p c z (Finsupp.degree (0 : Fin M →₀ ℕ) + 1) b) = 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact const_iterT hc0 hz _ b

/- English proof (translation)
Use extensionality with `α`. Establish `hT` using `agree_limT hp hc0 hz (Finsupp.degree α + 1)`. Establish `hlim0` using `const_limT hp hc0 hz`. Establish `hT0` using `const_iterT (p := p) hc0 hz (Finsupp.degree α + 1)`. Establish `h1 : coeff α (lgSum p c (limT p c z) b) = coeff α (lgSum p c (iterT p c z (Finsupp.degree α + 1)) b)` using `by show ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (limT p c z a ^ (p ^ n)) = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (iterT p c z (Finsupp.degree α + 1) a ^ (p ^ n))`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Establish `hpn : p ^ n = (p ^ n - 1) + 1` using `(Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm`.

Rewrite using `[hpn, agree_pow_succ (hlim0 a) (hT0 a) (hT a) _ α (Nat.lt_succ_self _)]`. Establish `h2 : coeff α (Phi p c z (iterT p c z (Finsupp.degree α + 1)) b) = coeff α (iterT p c z (Finsupp.degree α + 1) b)` using `(agree_iterT hp hc0 hz (Finsupp.degree α + 1) b α (Nat.lt_succ_self _)).symm`. Simplify using `only [Phi, map_add, map_sub] at h2`. Rewrite using `[h1]`. Take the linear combination `-h2`.
-/
theorem lgSum_limT (b : Fin d) : lgSum p c (limT p c z) b = z b := by
  ext α

  have hT := agree_limT hp hc0 hz (Finsupp.degree α + 1)
  have hlim0 := const_limT hp hc0 hz
  have hT0 := const_iterT (p := p) hc0 hz (Finsupp.degree α + 1)
  have h1 : coeff α (lgSum p c (limT p c z) b) =
      coeff α (lgSum p c (iterT p c z (Finsupp.degree α + 1)) b) := by
    show ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (limT p c z a ^ (p ^ n)) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1),
        ∑ a, c a n b * coeff α (iterT p c z (Finsupp.degree α + 1) a ^ (p ^ n))
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro a _
    have hpn : p ^ n = (p ^ n - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hpn, agree_pow_succ (hlim0 a) (hT0 a) (hT a) _ α (Nat.lt_succ_self _)]
  have h2 : coeff α (Phi p c z (iterT p c z (Finsupp.degree α + 1)) b) =
      coeff α (iterT p c z (Finsupp.degree α + 1) b) :=
    (agree_iterT hp hc0 hz (Finsupp.degree α + 1) b α (Nat.lt_succ_self _)).symm
  simp only [Phi, map_add, map_sub] at h2
  rw [h1]
  linear_combination -h2

end

end

end GlobalTheory.DepthRadii

namespace GlobalTheory.DepthRadii

variable {C : Type} [Field C] {d M : ℕ}

/- English proof (translation)
Introduce `α`. Rewrite using `[coeff_Phi hc0]`. Apply `AddValuation.map_le_sub v (hzb b α)` to reduce the goal to its premises. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `n _`.

Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `a _`. Distinguish the cases in `hne : c a (n + 1) b = 0`. Rewrite using `[hne, zero_mul, AddValuation.map_zero]`. Conclude with `le_top`.

Establish `h1` using `term_bound v hp dp c hdp hc hgood a (n + 1) b (by omega) hne`. Establish `h2` using `ordGe_pow (hs a) (p ^ (n + 1)) α`. Rewrite using `[AddValuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithTop.coe_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := add_le_add h1 h2`.
-/
theorem ordGe_Phi {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {p : ℕ} (hp : 3 ≤ p)
    {c : Fin d → ℕ → Fin d → C} (hc0 : ∀ a, c a 0 = Pi.single a 1) (dp : Fin d → ℤ)
    (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    {z s : Fin d → MvPowerSeries (Fin M) C} (hzb : ∀ b, OrdGe v ρ (z b) (radius p (dp b)))
    (hs : ∀ b, OrdGe v ρ (s b) (radius p (dp b))) (b : Fin d) :
    OrdGe v ρ (Phi p c z s b) (radius p (dp b)) := by
  intro α
  rw [coeff_Phi hc0]
  apply AddValuation.map_le_sub v (hzb b α)
  apply AddValuation.map_le_sum
  intro n _
  apply AddValuation.map_le_sum
  intro a _
  by_cases hne : c a (n + 1) b = 0
  · rw [hne, zero_mul, AddValuation.map_zero]; exact le_top
  have h1 := term_bound v hp dp c hdp hc hgood a (n + 1) b (by omega) hne
  have h2 := ordGe_pow (hs a) (p ^ (n + 1)) α
  rw [AddValuation.map_mul]
  calc ((radius p (dp b) - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ)
      = ((radius p (dp b) - (p : ℝ) ^ (n + 1) * radius p (dp a) : ℝ) : WithTop ℝ) +
        ((((p ^ (n + 1) : ℕ) : ℝ) * radius p (dp a) - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]; congr 1; push_cast; ring
    _ ≤ _ := add_le_add h1 h2

end GlobalTheory.DepthRadii

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `b α`. Use `show _ ≤ v (coeff α (0 : MvPowerSeries (Fin M) C))`.

Rewrite using `[map_zero, AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `succ k ih`. Introduce `b`. Conclude with `GlobalTheory.DepthRadii.ordGe_Phi hp hc0 dp hdp hc hgood hzb ih b`.
-/
private theorem ordGe_iterT {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d M : ℕ}
    {ρ : Fin M → ℝ} {p : ℕ} (hp : 3 ≤ p) {c : Fin d → ℕ → Fin d → C}
    (hc0 : ∀ a, c a 0 = Pi.single a 1) (dp : Fin d → ℤ) (hdp : ∀ a, -1 ≤ dp a)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b))
    {z : Fin d → MvPowerSeries (Fin M) C} (hzb : ∀ b, OrdGe v ρ (z b) (radius p (dp b))) :
    ∀ (k : ℕ) (b : Fin d), OrdGe v ρ (GlobalTheory.DepthRadii.iterT p c z k b) (radius p (dp b)) := by
  intro k
  induction k with
  | zero =>
    intro b α
    show _ ≤ v (coeff α (0 : MvPowerSeries (Fin M) C))
    rw [map_zero, AddValuation.map_zero]
    exact le_top
  | succ k ih =>
    intro b
    exact GlobalTheory.DepthRadii.ordGe_Phi hp hc0 dp hdp hc hgood hzb ih b

/- English proof (translation)
Establish `hprod : ∀ β : Fin d →₀ ℕ, OrdGe v ρ (β.prod fun s e => t s ^ e) 0`. Introduce `β`. Establish `key : ∀ s : Finset (Fin d), OrdGe v ρ (∏ i ∈ s, t i ^ β i) 0`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => rw [Finset.prod_empty]`. Conclude with `GlobalTheory.DepthRadii.ordGe_one`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi]`. Establish `h1` using `GlobalTheory.DepthRadii.ordGe_mono (GlobalTheory.DepthRadii.ordGe_pow (ht i) (β i)) (mul_zero ((β i : ℕ) : ℝ)).symm.le`.

Use `GlobalTheory.DepthRadii.ordGe_mul h1 ih` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis. Conclude with `key β.support`. Introduce `α`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]`.

Apply `finsum_induction (fun x => ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v x)` to reduce the goal to its premises. Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`. Introduce `x y hx hy`. Conclude with `le_trans (le_min hx hy) (AddValuation.map_add v x y)`.

Introduce `β`. Rewrite using `[smul_eq_mul, AddValuation.map_mul]`. Establish `h1 : (0 : WithTop ℝ) ≤ v (coeff β f)` using `hf β`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem ordGe_subst' {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d M : ℕ}
    {ρ : Fin M → ℝ} {t : Fin d → MvPowerSeries (Fin M) C}
    (ht0 : ∀ b, constantCoeff (t b) = 0) (ht : ∀ b, OrdGe v ρ (t b) 0)
    (f : MvPowerSeries (Fin d) C) (hf : MvIsInt v f) : OrdGe v ρ (subst t f) 0 := by

  have hprod : ∀ β : Fin d →₀ ℕ, OrdGe v ρ (β.prod fun s e => t s ^ e) 0 := by
    intro β
    have key : ∀ s : Finset (Fin d), OrdGe v ρ (∏ i ∈ s, t i ^ β i) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact GlobalTheory.DepthRadii.ordGe_one
      | insert i s hi ih =>
        rw [Finset.prod_insert hi]
        have h1 := GlobalTheory.DepthRadii.ordGe_mono (GlobalTheory.DepthRadii.ordGe_pow (ht i) (β i))
          (mul_zero ((β i : ℕ) : ℝ)).symm.le
        have := GlobalTheory.DepthRadii.ordGe_mul h1 ih
        rwa [add_zero] at this
    exact key β.support
  intro α
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]
  apply finsum_induction (fun x => ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤ v x)
  · rw [AddValuation.map_zero]; exact le_top
  · intro x y hx hy
    exact le_trans (le_min hx hy) (AddValuation.map_add v x y)
  · intro β
    rw [smul_eq_mul, AddValuation.map_mul]
    have h1 : (0 : WithTop ℝ) ≤ v (coeff β f) := hf β
    calc ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ)
        = 0 + ((0 - ∑ m, ρ m * ((α m : ℕ) : ℝ) : ℝ) : WithTop ℝ) := (zero_add _).symm
      _ ≤ _ := add_le_add h1 (hprod β α)

/- English proof (translation)
Introduce `C _ _ _ v p _ hp hvp d M dp c hdp hc0 hc hgood ρ hρ z hz hzb`. Establish `hlim : ∀ b, OrdGe v ρ (GlobalTheory.DepthRadii.limT p c z b) (radius p (dp b))`. Introduce `b α`. Conclude with `ordGe_iterT hp hc0 dp hdp hc hgood hzb (Finsupp.degree α + 1) b α`. Use `⟨GlobalTheory.DepthRadii.limT p c z, GlobalTheory.DepthRadii.const_limT hp hc0 hz, GlobalTheory.DepthRadii.lgSum_limT hp hc0 hz, hlim, ?_⟩` and prove the remaining obligations.

Introduce `f hf`. Conclude with `ordGe_subst' (GlobalTheory.DepthRadii.const_limT hp hc0 hz) (fun b => GlobalTheory.DepthRadii.ordGe_mono (hlim b) (GlobalTheory.DepthRadii.radius_pos hp _)) f hf`.
-/
theorem GlobalTheory.DepthRadii.exists_solution_ordGe_radius : LowBStatement := by
  intro C _ _ _ v p _ hp hvp d M dp c hdp hc0 hc hgood ρ hρ z hz hzb
  have hlim : ∀ b, OrdGe v ρ (GlobalTheory.DepthRadii.limT p c z b) (radius p (dp b)) := by
    intro b α
    exact ordGe_iterT hp hc0 dp hdp hc hgood hzb (Finsupp.degree α + 1) b α
  refine ⟨GlobalTheory.DepthRadii.limT p c z, GlobalTheory.DepthRadii.const_limT hp hc0 hz,
    GlobalTheory.DepthRadii.lgSum_limT hp hc0 hz, hlim, ?_⟩
  intro f hf
  exact ordGe_subst' (GlobalTheory.DepthRadii.const_limT hp hc0 hz)
    (fun b => GlobalTheory.DepthRadii.ordGe_mono (hlim b) (GlobalTheory.DepthRadii.radius_pos hp _)) f hf
