import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section PairJetAux

/- English proof (translation)
Unfold `mfact`. Conclude with `Finsupp.prod_fintype _ _ (fun _ => rfl)`.
-/
lemma mfact_eq_prod_univ {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) :
    mfact κ = ∏ x, (κ x).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => rfl)

/- English proof (translation)
Rewrite using `[mfact_eq_prod_univ, mfact_eq_prod_univ, mfact_eq_prod_univ, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_dvd_prod_of_dvd _ _ fun x _ => Nat.factorial_mul_factorial_dvd_factorial_add _ _`.
-/
lemma mfact_mul_dvd {σ : Type} [Fintype σ] (μ ν : σ →₀ ℕ) :
    mfact μ * mfact ν ∣ mfact (μ + ν) := by
  rw [mfact_eq_prod_univ, mfact_eq_prod_univ, mfact_eq_prod_univ, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun x _ =>
    Nat.factorial_mul_factorial_dvd_factorial_add _ _

def pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) : (Bool × ι) →₀ ℕ :=
  ∑ i, n i • (Finsupp.single (false, i) 1 + Finsupp.single (true, i) 1)

/- English proof (translation)
Unfold `pairExp`. Rewrite using `[Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Apply the tactic sequence `cases b <;> simp`. Introduce `j _ hj`.

Apply the tactic sequence `cases b <;> simp [hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
lemma pairExp_apply {ι : Type} [Fintype ι] (n : ι → ℕ) (b : Bool) (i : ι) :
    pairExp n (b, i) = n i := by
  classical
  unfold pairExp
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj
    cases b <;> simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Rewrite using `[mfact_eq_prod_univ, Fintype.prod_prod_type, Fintype.prod_bool]`. Simplify using `only [pairExp_apply]`.
-/
lemma mfact_pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) :
    mfact (pairExp n) = (∏ i, (n i).factorial) * ∏ i, (n i).factorial := by
  classical
  rw [mfact_eq_prod_univ, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [pairExp_apply]

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

/- English proof (translation)
Rewrite using `[Finset.sum_pow_eq_sum_piAntidiag]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `pairExp`. Rewrite using `[← MvPowerSeries.prod_monomial]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← MvPowerSeries.monomial_pow]`. Use `congr 1`. Rewrite using `[MvPowerSeries.X_def, MvPowerSeries.X_def, ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]`. Simplify using the standard rewrite rules.
-/
lemma quad_pow {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → K) (k : ℕ) :
    (∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) :
      MvPowerSeries (Bool × ι) K) ^ k =
    ∑ n ∈ Finset.piAntidiag Finset.univ k, (Nat.multinomial Finset.univ n : MvPowerSeries (Bool × ι) K) *
      MvPowerSeries.monomial (pairExp n) (∏ i, u i ^ n i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  unfold pairExp
  rw [← MvPowerSeries.prod_monomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← MvPowerSeries.monomial_pow]
  congr 1
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ r` using `by linarith`. Establish `hQ0 : MvPowerSeries.constantCoeff ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K) = 0`. Simplify using the standard rewrite rules. Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero hQ0`. Unfold `mvExp`.

Rewrite using `[PowerSeries.coeff_subst hs, mul_finsum]`. Use `norm_finsum_le_of (pow_nonneg hr0 _) fun k => ?_` and prove the remaining obligations. Rewrite using `[smul_pow, quad_pow, PowerSeries.coeff_exp, Finset.smul_sum, map_sum, Finset.smul_sum, Finset.mul_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[Finset.mem_piAntidiag]`.

Establish `hk : ∑ i, n i = k` using `hn.1`. Rewrite using `[← map_natCast (MvPowerSeries.C (σ := Bool × ι) (R := K)), ← MvPowerSeries.smul_eq_C_mul, map_smul, map_smul, MvPowerSeries.coeff_monomial]`. Distinguish the cases in `hκ : κ = pairExp n`. Rewrite using `[if_pos hκ]`. Establish `hspec` using `Nat.multinomial_spec Finset.univ n`.

Rewrite `hspec` using `[hk]`. Establish `hk0 : ((k.factorial : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)`. Establish `hval : ((mfact κ : ℕ) : K) * ((algebraMap ℚ K) (1 / (k.factorial : ℚ)) • ((-S) ^ k • ((Nat.multinomial Finset.univ n : ℕ) : K) • ∏ i, u i ^ n i)) = ((∏ i, (n i).factorial : ℕ) : K) * ((-S) ^ k * ∏ i, u i ^ n i)`. Rewrite using `[hκ, mfact_pairExp, map_div₀, map_one, map_natCast, ← hspec]`. Rewrite `hk0` using `[← hspec]`.

Simplify using `only [smul_eq_mul]`. Move the coercions through the operations in `at hk0 ⊢`. Establish `hP` using `left_ne_zero_of_mul hk0`. Establish `hM` using `right_ne_zero_of_mul hk0`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hval, norm_mul, norm_mul, norm_pow, norm_neg, norm_prod]`. Establish `h1 : ‖((∏ i, (n i).factorial : ℕ) : K)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one K _`. Establish `h2 : ∏ i, ‖u i ^ n i‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (hu i)`.

Establish `h3 : ‖S‖ ^ k ≤ r ^ k` using `pow_le_pow_left₀ (norm_nonneg _) hS k`. Establish `h4 : ∑ i, min (κ (false, i)) (κ (true, i)) = k`. Rewrite using `[hκ, ← hk]`. Simplify using `only [pairExp_apply, min_self]`. Rewrite using `[h4]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul h1 _ (by positivity) zero_le_one` to reduce the goal to its premises. Conclude with `mul_le_mul h3 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _)`. Use `_ = r ^ k := by ring`. Rewrite using `[if_neg hκ]`.

Simplify using `only [smul_zero, mul_zero, norm_zero]`. Conclude with `pow_nonneg hr0 _`.
-/
lemma exp_jet (r : ℝ) (hr : 1 ≤ r) (ι : Type) [Fintype ι] (S : K) (u : ι → K) (hS : ‖S‖ ≤ r)
    (hu : ∀ i, ‖u i‖ ≤ 1) (κ : (Bool × ι) →₀ ℕ) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i)))‖ ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
  classical
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hQ0 : MvPowerSeries.constantCoeff ((-S) • ∑ i, MvPowerSeries.C (u i) *
      MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  unfold mvExp
  rw [PowerSeries.coeff_subst hs, mul_finsum]
  refine norm_finsum_le_of (pow_nonneg hr0 _) fun k => ?_
  rw [smul_pow, quad_pow, PowerSeries.coeff_exp, Finset.smul_sum, map_sum, Finset.smul_sum,
    Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
  rw [Finset.mem_piAntidiag] at hn
  have hk : ∑ i, n i = k := hn.1
  rw [← map_natCast (MvPowerSeries.C (σ := Bool × ι) (R := K)), ← MvPowerSeries.smul_eq_C_mul,
    map_smul, map_smul, MvPowerSeries.coeff_monomial]
  by_cases hκ : κ = pairExp n
  · rw [if_pos hκ]
    have hspec := Nat.multinomial_spec Finset.univ n
    rw [hk] at hspec
    have hk0 : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hval : ((mfact κ : ℕ) : K) * ((algebraMap ℚ K) (1 / (k.factorial : ℚ)) •
        ((-S) ^ k • ((Nat.multinomial Finset.univ n : ℕ) : K) • ∏ i, u i ^ n i)) =
        ((∏ i, (n i).factorial : ℕ) : K) * ((-S) ^ k * ∏ i, u i ^ n i) := by
      rw [hκ, mfact_pairExp, map_div₀, map_one, map_natCast, ← hspec]
      rw [← hspec] at hk0
      simp only [smul_eq_mul]
      push_cast at hk0 ⊢
      have hP := left_ne_zero_of_mul hk0
      have hM := right_ne_zero_of_mul hk0
      field_simp
    rw [hval, norm_mul, norm_mul, norm_pow, norm_neg, norm_prod]
    have h1 : ‖((∏ i, (n i).factorial : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
    have h2 : ∏ i, ‖u i ^ n i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu i)
    have h3 : ‖S‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hS k
    have h4 : ∑ i, min (κ (false, i)) (κ (true, i)) = k := by
      rw [hκ, ← hk]
      simp only [pairExp_apply, min_self]
    rw [h4]
    calc ‖((∏ i, (n i).factorial : ℕ) : K)‖ * (‖S‖ ^ k * ∏ i, ‖u i ^ n i‖)
        ≤ 1 * (r ^ k * 1) := by
          apply mul_le_mul h1 _ (by positivity) zero_le_one
          exact mul_le_mul h3 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _)
      _ = r ^ k := by ring
  · rw [if_neg hκ]
    simp only [smul_zero, mul_zero, norm_zero]
    exact pow_nonneg hr0 _

end PairJetAux

/- English proof (translation)
Introduce `K _ _ _ pi h0 h1 ι _ S u hS hu sg hsg κ`. Use `set r : ℝ := pi ^ (-(1 / 2 : ℝ)) with hrdef`. Establish `hr : 1 ≤ r` using `Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)`. Establish `hr0 : (0 : ℝ) ≤ r` using `by linarith`. Establish `hrhs : pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ)) = r ^ (∑ i, min (κ (false, i)) (κ (true, i)))`.

Rewrite using `[Real.rpow_mul h0.le, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hrhs, MvPowerSeries.coeff_mul, Finset.mul_sum]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Take `⟨c, hc⟩` from `mfact_mul_dvd p.1 p.2`. Rewrite `hc` using `[hp]`. Establish `hE` using `exp_jet r hr ι S u hS hu p.1`.

Establish `hG` using `hsg p.2`. Establish `hcn : ‖((c : ℕ) : K)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one K _`. Use `set E := mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K)`. Establish `hre : ((mfact κ : ℕ) : K) * (MvPowerSeries.coeff p.1 E * MvPowerSeries.coeff p.2 sg) = (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 E) * ((((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg) * ((c : ℕ) : K))`. Rewrite using `[hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre, norm_mul, norm_mul (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg)]`. Establish `hmono : r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i)))`. Apply `pow_le_pow_right₀ hr` to reduce the goal to its premises.

Apply `Finset.sum_le_sum fun i _ => ?_` to reduce the goal to its premises. Rewrite using `[← hp]`. Simplify using `only [Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul hE _ (by positivity) (pow_nonneg hr0 _)` to reduce the goal to its premises. Conclude with `mul_le_mul hG hcn (norm_nonneg _) zero_le_one`. Use `_ ≤ _ := by rw [mul_one, mul_one]; exact hmono`.
-/
theorem pair_jet_bound : PairJet.{u} := by
  intro K _ _ _ pi h0 h1 ι _ S u hS hu sg hsg κ
  classical
  set r : ℝ := pi ^ (-(1 / 2 : ℝ)) with hrdef
  have hr : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrhs : pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ)) =
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    rw [Real.rpow_mul h0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  rw [hrhs, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨c, hc⟩ := mfact_mul_dvd p.1 p.2
  rw [hp] at hc
  have hE := exp_jet r hr ι S u hS hu p.1
  have hG := hsg p.2
  have hcn : ‖((c : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
  set E := mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K)
  have hre : ((mfact κ : ℕ) : K) * (MvPowerSeries.coeff p.1 E * MvPowerSeries.coeff p.2 sg) =
      (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 E) *
        ((((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg) * ((c : ℕ) : K)) := by
    rw [hc]; push_cast; ring
  rw [hre, norm_mul, norm_mul (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg)]
  have hmono : r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) ≤
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    apply pow_le_pow_right₀ hr
    apply Finset.sum_le_sum fun i _ => ?_
    rw [← hp]
    simp only [Finsupp.add_apply]
    omega
  calc _ ≤ r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) * (1 * 1) := by
        apply mul_le_mul hE _ (by positivity) (pow_nonneg hr0 _)
        exact mul_le_mul hG hcn (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [mul_one, mul_one]; exact hmono

end Formalism.DworkPowerSeriesWeights
