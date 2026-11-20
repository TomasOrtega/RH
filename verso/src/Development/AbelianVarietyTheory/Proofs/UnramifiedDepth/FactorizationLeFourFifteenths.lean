import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : l ^ B.factorization l ≤ B` using `Nat.ordProj_le l hB`. Establish `h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l` using `Nat.pow_le_pow_left hl _`. Establish `h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ]`. Use linear arithmetic over natural numbers and integers. Establish `h4 : 4 * B.factorization l + 1 ≤ B` using `le_trans (h3 _) (le_trans h2 h1)`. Establish `h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B` using `by exact_mod_cast h4`.

Establish `h6 : (0 : ℝ) ≤ (B.factorization l : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem factorization_le_four_fifteenths {l B : ℕ} (hl : 5 ≤ l) (hB : B ≠ 0) :
    (B.factorization l : ℝ) ≤ 4 / 15 * (B : ℝ) := by
  have h1 : l ^ B.factorization l ≤ B := Nat.ordProj_le l hB
  have h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l := Nat.pow_le_pow_left hl _
  have h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h4 : 4 * B.factorization l + 1 ≤ B := le_trans (h3 _) (le_trans h2 h1)
  have h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (B.factorization l : ℝ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Establish `h1 : x ≤ x ^ i`. Simplify using `using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi`. Establish `h2 : 1 / (8 * x ^ i) ≤ 1 / 40` using `one_div_le_one_div_of_le (by norm_num) (by linarith)`. Establish `hp : 0 < x ^ 2 - 1` using `by nlinarith`. Establish `hq : 0 < x - 1` using `by linarith`.

Establish `h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1)`. Establish `: x ^ 2 - 1 = (x - 1) * (x + 1)` using `by ring`. Rewrite using `[this]`. Establish `hr : 0 < x + 1` using `by linarith`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : x / (x ^ 2 - 1) ≤ 5 / 24`. Rewrite using `[div_le_div_iff₀ hp (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem four_fifteenths_le_slope_gap {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by
  have h1 : x ≤ x ^ i := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi
  have h2 : 1 / (8 * x ^ i) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < x - 1 := by linarith
  have h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    have hr : 0 < x + 1 := by linarith
    field_simp
    ring
  have h4 : x / (x ^ 2 - 1) ≤ 5 / 24 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    nlinarith
  linarith

/- English proof (translation)
Introduce `C _ _ v l hl hv h5 i κ κ' _ _ _ _ h₁ hi hsupp hder α`. Distinguish the cases in `h0 : MvPowerSeries.coeff α h₁ = 0`. Rewrite using `[h0, v.map_zero]`. Conclude with `le_top`. Take `⟨b, hb⟩` from `hsupp α h0`.

Choose the witnesses or unpack the hypotheses as in `⟨β, rfl⟩ : ∃ β : κ ⊕ κ' →₀ ℕ, α = β + Finsupp.single (Sum.inr b) 1 := by`. Use `⟨α - Finsupp.single (Sum.inr b) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[tsub_add_cancel_of_le]`. Conclude with `Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hb)`. Establish `h` using `hder b β`.

Establish `hc : ((β (Sum.inr b) : C) + 1) = ((β (Sum.inr b) + 1 : ℕ) : C)` using `by push_cast; rfl`. Rewrite `h` using `[MvPowerSeries.coeff_pderiv, hc, v.map_mul, ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (Nat.succ_ne_zero _)]`. Establish `hf` using `factorization_le_four_fifteenths h5 (Nat.succ_ne_zero (β (Sum.inr b)))`. Establish `hg` using `four_fifteenths_le_slope_gap (x := (l : ℝ)) (by exact_mod_cast h5) hi`. Generalize the expression as in `v (MvPowerSeries.coeff (β + Finsupp.single (Sum.inr b) 1) h₁) = w at h ⊢`.

Proceed by induction on `w using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe w`. Rewrite `h` using `[← WithTop.coe_add, WithTop.coe_le_coe]`. Rewrite using `[WithTop.coe_le_coe]`.

Rewrite using `[Finsupp.sum_add_index' (by intro j; simp) (by intro j e e'; push_cast; ring), Finsupp.sum_single_index (by simp)]`. Rewrite `h`, the goal using `[Finsupp.sum_fintype _ _ (by intro j; simp), Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum] at h ⊢`. Establish `hJ : (β (Sum.inr b) : ℝ) ≤ ∑ q, (β (Sum.inr q) : ℝ)` using `Finset.single_le_sum (f := fun q => (β (Sum.inr q) : ℝ)) (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ b)`. Establish `hJ0 : (0 : ℝ) ≤ β (Sum.inr b)` using `Nat.cast_nonneg _`.

Move the coercions through the operations in `at hf ⊢`. Generalize the expression as in `(∑ q, (β (Sum.inr q) : ℝ)) = J at h hJ ⊢`. Generalize the expression as in `(1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) = c' at hg ⊢`. Generalize the expression as in `1 / ((l : ℝ) - 1) = c at h hg ⊢`. Establish `hm : 4 / 15 * (J + 1) ≤ (c' - c) * (J + 1)` using `mul_le_mul_of_nonneg_right hg (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weight_of_weight_pderiv :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i : ℕ) (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (h₁ : MvPowerSeries (κ ⊕ κ') C), 1 ≤ i →
    (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) → (∀ b, (∀ α, (((0) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) - 1)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.pderiv C (Sum.inr b) h₁)))) →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁)))) := by
  intro C _ _ v l hl hv h5 i κ κ' _ _ _ _ h₁ hi hsupp hder α
  by_cases h0 : MvPowerSeries.coeff α h₁ = 0
  · rw [h0, v.map_zero]; exact le_top
  obtain ⟨b, hb⟩ := hsupp α h0
  obtain ⟨β, rfl⟩ : ∃ β : κ ⊕ κ' →₀ ℕ, α = β + Finsupp.single (Sum.inr b) 1 := by
    refine ⟨α - Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hb)
  have h := hder b β
  have hc : ((β (Sum.inr b) : C) + 1) = ((β (Sum.inr b) + 1 : ℕ) : C) := by push_cast; rfl
  rw [MvPowerSeries.coeff_pderiv, hc, v.map_mul,
    ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (Nat.succ_ne_zero _)] at h
  have hf := factorization_le_four_fifteenths h5 (Nat.succ_ne_zero (β (Sum.inr b)))
  have hg := four_fifteenths_le_slope_gap (x := (l : ℝ)) (by exact_mod_cast h5) hi
  generalize v (MvPowerSeries.coeff (β + Finsupp.single (Sum.inr b) 1) h₁) = w at h ⊢
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe]
    rw [Finsupp.sum_add_index' (by intro j; simp) (by intro j e e'; push_cast; ring),
      Finsupp.sum_single_index (by simp)]
    rw [Finsupp.sum_fintype _ _ (by intro j; simp), Fintype.sum_sum_type] at h ⊢
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum] at h ⊢
    have hJ : (β (Sum.inr b) : ℝ) ≤ ∑ q, (β (Sum.inr q) : ℝ) :=
      Finset.single_le_sum (f := fun q => (β (Sum.inr q) : ℝ))
        (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ b)
    have hJ0 : (0 : ℝ) ≤ β (Sum.inr b) := Nat.cast_nonneg _
    push_cast at hf ⊢
    generalize (∑ q, (β (Sum.inr q) : ℝ)) = J at h hJ ⊢
    generalize (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) = c' at hg ⊢
    generalize 1 / ((l : ℝ) - 1) = c at h hg ⊢
    have hm : 4 / 15 * (J + 1) ≤ (c' - c) * (J + 1) :=
      mul_le_mul_of_nonneg_right hg (by linarith)
    nlinarith

end GlobalTheory
