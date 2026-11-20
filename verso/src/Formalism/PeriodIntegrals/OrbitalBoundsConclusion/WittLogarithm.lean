import Mathlib
import Formalism.PeriodIntegrals.InvSerSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.WfLogOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.FormalLogarithmHolds

/- English proof (translation)
Introduce `K _ S l ex hl hl0 hl1 hex0 hsub n`. Take `⟨c, hc⟩` from `PowerSeries.X_dvd_iff.2 hex0`. Establish `hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) = if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0`. Introduce `d m`. Rewrite using `[hc, mul_pow, PowerSeries.coeff_X_pow_mul']`.

Establish `hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex`. Introduce `j`. Rewrite using `[hc, PowerSeries.coeff_succ_X_mul]`. Establish `hHS : PowerSeries.HasSubst ex` using `by first`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero hex0`.

Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)`. Establish `key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) = ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d)`. Introduce `m`. Establish `hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) = ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)`.

Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [Function.mem_support] at hd`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[hpow, if_neg (by omega), smul_zero]`. Rewrite using `[← hsub, PowerSeries.coeff_subst' hHS, hfin]`. Simplify using `only [smul_eq_mul]`. Establish `hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) → ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S`.

Introduce `N hN d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `i _`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`.

Use `split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Consider the case `succ d ihd`. Introduce `i hi`.

Rewrite using `[pow_succ, PowerSeries.coeff_mul]`. Apply `Subring.sum_mem` to reduce the goal to its premises. Introduce `p hp`. Establish `h : p.1 + p.2 = i` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Conclude with `S.mul_mem (ihd _ (by omega)) (hN _ (by omega))`.

Establish `hl0' : PowerSeries.coeff 0 l = 0`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `n with _ | n` into its components or cases.

Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]`. Conclude with `S.zero_mem`. Establish `k` using `key (n + 1)`. Rewrite `k` using `[Finset.sum_range_succ', Finset.sum_range_succ']`. Simplify using `only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k`.

Establish `he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) - ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l * PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1))`. Rewrite using `[k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Apply `S.sub_mem` to reduce the goal to its premises.

Rewrite using `[PowerSeries.coeff_X] split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Apply `Subring.sum_mem` to reduce the goal to its premises. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_range]`. Apply `S.mul_mem (hl _)` to reduce the goal to its premises. Rewrite using `[hpow]`. Use `split_ifs with hle`. Apply `hB (n - 1) _ (i + 1 + 1) _ (by omega)` to reduce the goal to its premises.

Introduce `j hj`. Rewrite using `[hcoef]`. Conclude with `ih _ (by omega)`. Conclude with `S.zero_mem`.
-/
private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem

/- English proof (translation)
The claim follows from `PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds`.
-/
theorem witt_logarithm : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
