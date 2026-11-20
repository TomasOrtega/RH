import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Development

noncomputable section

open Classical PowerSeries

namespace PI.BeConjNormW

namespace InverseCommuting

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `first`. Consider the case `exact Iff.rfl`. Consider the case `(simp only [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]; rfl)`. Consider the case `simp [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]`.
-/
theorem mem_integerRing_iff_norm_le_one (x : ℂ_[p]) : x ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p ↔ ‖x‖ ≤ 1 := by
  first
  | exact Iff.rfl
  | (simp only [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]; rfl)
  | simp [PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing]

/- English proof (translation)
Establish `hf' : ∀ m, coeff m f ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p` using `fun m => (mem_integerRing_iff_norm_le_one _).2 (hf m)`. Rewrite using `[← mem_integerRing_iff_norm_le_one]`. Proceed by induction on `k generalizing n with`. Consider the case `zero`. Rewrite using `[pow_zero, coeff_one]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Consider the case `succ k ih`. Rewrite using `[pow_succ, coeff_mul]`.

Conclude with `sum_mem fun x _ => mul_mem (ih _) (hf' _)`.
-/
theorem coeff_pow_int {f : PowerSeries ℂ_[p]} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k n : ℕ) :
    ‖coeff n (f ^ k)‖ ≤ 1 := by
  have hf' : ∀ m, coeff m f ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := fun m => (mem_integerRing_iff_norm_le_one _).2 (hf m)
  rw [← mem_integerRing_iff_norm_le_one]
  induction k generalizing n with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact sum_mem fun x _ => mul_mem (ih _) (hf' _)

/- English proof (translation)
Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.mpr hf0`. Rewrite using `[mul_pow, coeff_X_pow_mul', if_neg (by omega)]`.
-/
theorem coeff_pow_of_lt {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) {k n : ℕ} (h : n < k) :
    coeff n (f ^ k) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

/- English proof (translation)
Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.mpr hf0`. Establish `h1 : coeff 1 (X * g) = constantCoeff g`. Rewrite using `[show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[h1, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow]`.
-/
theorem coeff_pow_self {f : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (f ^ n) = coeff 1 f ^ n := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have h1 : coeff 1 (X * g) = constantCoeff g := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [h1, mul_pow, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow]

/- English proof (translation)
Establish `hs : HasSubst f` using `by first`. Consider the case `exact HasSubst.of_constantCoeff_zero' hf0`. Consider the case `exact HasSubst.of_constantCoeff_zero hf0`. Establish `h1 : coeff n (subst f g) = ∑ᶠ k : ℕ, coeff k g * coeff n (f ^ k)` using `by first`. Consider the case `exact (coeff_subst hs g (Finsupp.single () n)).trans (finsum_congr fun k => smul_eq_mul _ _)`.

Consider the case `(rw [coeff_subst' hs]; simp only [smul_eq_mul])`. Rewrite using `[h1, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]`. Introduce `k hk`. Rewrite `hk` using `[Function.mem_support]`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `h`. Conclude with `hk (by rw [coeff_pow_of_lt hf0 (by omega), mul_zero])`.
-/
theorem coeff_subst_fin {f g : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (subst f g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (f ^ k) := by
  have hs : HasSubst f := by
    first
    | exact HasSubst.of_constantCoeff_zero' hf0
    | exact HasSubst.of_constantCoeff_zero hf0
  have h1 : coeff n (subst f g) = ∑ᶠ k : ℕ, coeff k g * coeff n (f ^ k) := by
    first
    | exact (coeff_subst hs g (Finsupp.single () n)).trans (finsum_congr fun k => smul_eq_mul _ _)
    | (rw [coeff_subst' hs]; simp only [smul_eq_mul])
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  intro k hk
  rw [Function.mem_support] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hk (by rw [coeff_pow_of_lt hf0 (by omega), mul_zero])

end InverseCommuting

open InverseCommuting in
/- English proof (translation)
Introduce `p _ f g hf0 hg0 h1 hf hfg n`. Establish `key : ∀ m, coeff m g ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Rewrite using `[coeff_zero_eq_constantCoeff_apply, hg0]`. Conclude with `zero_mem _`. Establish `hs` using `coeff_subst_fin (g := g) hf0 m`. Rewrite `hs` using `[hfg, Finset.sum_range_succ, coeff_pow_self hf0]`.

Establish `hrest : (∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k)) ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p` using `sum_mem fun k hk => mul_mem (ih k (Finset.mem_range.mp hk)) ((mem_integerRing_iff_norm_le_one _).2 (coeff_pow_int hf k m))`. Establish `hX : coeff m (X : PowerSeries ℂ_[p]) ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p`. Rewrite using `[coeff_X]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `hprod : coeff m g * coeff 1 f ^ m ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p`. Establish `he : coeff m g * coeff 1 f ^ m = coeff m (X : PowerSeries ℂ_[p]) - ∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k)`. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[he]`. Conclude with `sub_mem hX hrest`. Rewrite `hprod`, the goal using `[mem_integerRing_iff_norm_le_one]`. Rewrite `hprod` using `[norm_mul, norm_pow, h1, one_pow, mul_one]`. Then use the resulting hypothesis. Conclude with `(mem_integerRing_iff_norm_le_one _).1 (key n)`.
-/
theorem inverse_integral_padic : IntInv := by
  intro p _ f g hf0 hg0 h1 hf hfg n
  have key : ∀ m, coeff m g ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [coeff_zero_eq_constantCoeff_apply, hg0]
        exact zero_mem _
      · have hs := coeff_subst_fin (g := g) hf0 m
        rw [hfg, Finset.sum_range_succ, coeff_pow_self hf0] at hs
        have hrest : (∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k)) ∈
            PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p :=
          sum_mem fun k hk => mul_mem (ih k (Finset.mem_range.mp hk)) ((mem_integerRing_iff_norm_le_one _).2 (coeff_pow_int hf k m))
        have hX : coeff m (X : PowerSeries ℂ_[p]) ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          rw [coeff_X]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have hprod : coeff m g * coeff 1 f ^ m ∈ PI.PhNormUnits.UnitaryGroupMassFormula.PAdicPowerSeriesCoefficients.intRing p := by
          have he : coeff m g * coeff 1 f ^ m =
              coeff m (X : PowerSeries ℂ_[p]) - ∑ k ∈ Finset.range m, coeff k g * coeff m (f ^ k) := by
            rw [hs]
            ring
          rw [he]
          exact sub_mem hX hrest
        rw [mem_integerRing_iff_norm_le_one] at hprod ⊢
        rwa [norm_mul, norm_pow, h1, one_pow, mul_one] at hprod
  exact (mem_integerRing_iff_norm_le_one _).1 (key n)

end PI.BeConjNormW
