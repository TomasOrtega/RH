import Mathlib
import Formalism.PeriodIntegrals.PhNormLimit

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro e he`. Conclude with `absurd he (Nat.not_lt_zero _)`. Consider the case `succ d ih`.

Introduce `e he`. Rewrite using `[pow_succ, MvPowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Establish `hsum : x.1 () + x.2 () = e ()`.

Rewrite using `[← Finsupp.add_apply, Finset.HasAntidiagonal.mem_antidiagonal.mp hx]`. Distinguish the cases in `h0 : x.2 () = 0`. Establish `hx2 : x.2 = 0`. Use `ext`. Simplify using `using h0`.

Rewrite using `[hx2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha, mul_zero]`. Rewrite using `[ih x.1 (by omega), zero_mul]`.
-/
private theorem coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero {K : Type*} [CommRing K] (a : MvPowerSeries Unit K)
    (ha : MvPowerSeries.constantCoeff a = 0) :
    ∀ (d : ℕ) (e : Unit →₀ ℕ), e () < d → MvPowerSeries.coeff e (a ^ d) = 0 := by
  intro d
  induction d with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ d ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hsum : x.1 () + x.2 () = e () := by
      rw [← Finsupp.add_apply, Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
    by_cases h0 : x.2 () = 0
    · have hx2 : x.2 = 0 := by
        ext
        simpa using h0
      rw [hx2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha, mul_zero]
    · rw [ih x.1 (by omega), zero_mul]

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [Function.mem_support, ne_eq] at hd`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `hn`. Conclude with `hd (by rw [coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero a ha d e (by omega), smul_zero])`.
-/
private theorem coeff_subst_eq_sum_range_coeff_mul_coeff_pow {K : Type*} [CommRing K] (f : PowerSeries K)
    (a : MvPowerSeries Unit K) (ha : MvPowerSeries.constantCoeff a = 0) (e : Unit →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) =
      ∑ d ∈ Finset.range (e () + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hn
  exact hd (by rw [coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero a ha d e (by omega), smul_zero])

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum_range_coeff_mul_coeff_pow f a ha 0]`. Simplify using the standard rewrite rules.
-/
private theorem constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion {K : Type*} [CommRing K] (f : PowerSeries K)
    (a : MvPowerSeries Unit K) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst_eq_sum_range_coeff_mul_coeff_pow f a ha 0]
  simp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `e`. Simplify using `only [pow_zero]`.

Conclude with `continuous_const`. Consider the case `succ n ih`. Introduce `e`. Simplify using `only [pow_succ, MvPowerSeries.coeff_mul]`. Conclude with `continuous_finset_sum _ fun x _ => (ih x.1).mul (hF x.2)`.
-/
private theorem continuous_coeff_pow_of_continuous_coeff {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (F : Y → MvPowerSeries Unit K) (hF : ∀ e, Continuous fun y => MvPowerSeries.coeff e (F y)) :
    ∀ (n : ℕ) (e : Unit →₀ ℕ), Continuous fun y => MvPowerSeries.coeff e (F y ^ n) := by
  intro n
  induction n with
  | zero =>
    intro e
    simp only [pow_zero]
    exact continuous_const
  | succ n ih =>
    intro e
    simp only [pow_succ, MvPowerSeries.coeff_mul]
    exact continuous_finset_sum _ fun x _ => (ih x.1).mul (hF x.2)

/- English proof (translation)
Introduce `e`. Establish `h : (fun y => MvPowerSeries.coeff e (PowerSeries.subst (a y) f)) = fun y => ∑ d ∈ Finset.range (e () + 1), PowerSeries.coeff d f • MvPowerSeries.coeff e (a y ^ d)`. Use function extensionality and compare the values at `fun y => coeff_subst_eq_sum_range_coeff_mul_coeff_pow f (a y) (ha y) e`. Rewrite using `[h]`. Conclude with `continuous_finset_sum _ fun d _ => Continuous.smul (f := fun _ => PowerSeries.coeff d f) continuous_const (continuous_coeff_pow_of_continuous_coeff a hc d e)`.
-/
private theorem continuous_coeff_subst_of_continuous_coeff {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (f : PowerSeries K) (a : Y → MvPowerSeries Unit K)
    (ha : ∀ y, MvPowerSeries.constantCoeff (a y) = 0)
    (hc : ∀ e, Continuous fun y => MvPowerSeries.coeff e (a y)) :
    ∀ e, Continuous fun y => MvPowerSeries.coeff e (PowerSeries.subst (a y) f) := by
  intro e
  have h : (fun y => MvPowerSeries.coeff e (PowerSeries.subst (a y) f)) =
      fun y => ∑ d ∈ Finset.range (e () + 1),
        PowerSeries.coeff d f • MvPowerSeries.coeff e (a y ^ d) :=
    funext fun y => coeff_subst_eq_sum_range_coeff_mul_coeff_pow f (a y) (ha y) e
  rw [h]
  exact continuous_finset_sum _ fun d _ =>
    Continuous.smul (f := fun _ => PowerSeries.coeff d f) continuous_const (continuous_coeff_pow_of_continuous_coeff a hc d e)

/- English proof (translation)
Introduce `_ hy` and use `closure_minimal h hc hy`.
-/
private theorem forall_mem_closure_of_isClosed_setOf {Y : Type*} [TopologicalSpace Y] (T : Set Y) (P : Y → Prop)
    (hc : IsClosed {y | P y}) (h : ∀ y ∈ T, P y) : ∀ y ∈ closure T, P y :=
  fun _ hy => closure_minimal h hc hy

/- English proof (translation)
Establish `h1 : IsClosed {y | MvPowerSeries.constantCoeff (F y) = 0}`. Use `isClosed_eq ?_ continuous_const` and prove the remaining obligations. Simplify `hF 0` using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Establish `h2 : IsClosed {y | ∀ n : Unit →₀ ℕ, ‖MvPowerSeries.coeff n (G y)‖ ≤ 1}`. Simplify using `only [Set.setOf_forall]`.

Use `isClosed_iInter fun n => isClosed_le ?_ continuous_const` and prove the remaining obligations. Simplify using `only [hG]`. Conclude with `(continuous_finset_sum _ fun k _ => (continuous_coeff_pow_of_continuous_coeff F hF k n).div_const _).norm`. Simplify `h1.inter h2` using `only [Set.setOf_and]`.
-/
private theorem isClosed_setOf_coeff_exp_norm_le_one {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (F G : Y → MvPowerSeries Unit K) (hF : ∀ e, Continuous fun y => MvPowerSeries.coeff e (F y))
    (hG : ∀ (n : Unit →₀ ℕ) (y : Y), MvPowerSeries.coeff n (G y) =
      ∑ k ∈ Finset.range ((n.sum fun _ k => k) + 1),
        MvPowerSeries.coeff n (F y ^ k) / (k.factorial : K)) :
    IsClosed {y | MvPowerSeries.constantCoeff (F y) = 0 ∧
      ∀ n : Unit →₀ ℕ, ‖MvPowerSeries.coeff n (G y)‖ ≤ 1} := by
  have h1 : IsClosed {y | MvPowerSeries.constantCoeff (F y) = 0} := by
    refine isClosed_eq ?_ continuous_const
    simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hF 0
  have h2 : IsClosed {y | ∀ n : Unit →₀ ℕ, ‖MvPowerSeries.coeff n (G y)‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun n => isClosed_le ?_ continuous_const
    simp only [hG]
    exact (continuous_finset_sum _ fun k _ => (continuous_coeff_pow_of_continuous_coeff F hF k n).div_const _).norm
  simpa only [Set.setOf_and] using h1.inter h2

/- English proof (translation)
Establish `hin : ∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0`. Introduce `y`. Rewrite using `[map_mul, MvPowerSeries.constantCoeff_C, constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l _ (MvPowerSeries.constantCoeff_X ()), hl, mul_zero]`. Establish `hmid : ∀ y, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) = 0` using `fun y => (constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion ex _ (hin y)).trans hex`. Use `continuous_coeff_subst_of_continuous_coeff ph _ hmid ?_` and prove the remaining obligations.

Use `continuous_coeff_subst_of_continuous_coeff ex _ hin ?_` and prove the remaining obligations. Introduce `e`. Simplify using `only [MvPowerSeries.coeff_C_mul]`. Conclude with `hc.mul continuous_const`.
-/
private theorem continuous_coeff_subst_subst_C_mul_subst {K Y : Type*} [NormedField K] [TopologicalSpace Y]
    (l ex ph : PowerSeries K) (hl : PowerSeries.constantCoeff l = 0)
    (hex : PowerSeries.constantCoeff ex = 0) (c : Y → K) (hc : Continuous c) :
    ∀ e, Continuous fun y => MvPowerSeries.coeff e (PowerSeries.subst (PowerSeries.subst
        (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l)
        ex) ph) := by
  have hin : ∀ y, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    intro y
    rw [map_mul, MvPowerSeries.constantCoeff_C,
      constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l _ (MvPowerSeries.constantCoeff_X ()), hl, mul_zero]
  have hmid : ∀ y, MvPowerSeries.constantCoeff (PowerSeries.subst
      (MvPowerSeries.C (c y) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l)
      ex) = 0 :=
    fun y => (constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion ex _ (hin y)).trans hex
  refine continuous_coeff_subst_of_continuous_coeff ph _ hmid ?_
  refine continuous_coeff_subst_of_continuous_coeff ex _ hin ?_
  intro e
  simp only [MvPowerSeries.coeff_C_mul]
  exact hc.mul continuous_const

/- English proof (translation)
Unfold `PI.PhNormLimit.Target`. Introduce `p _ l ex ph T h0 h1 _ h3`. Establish `hl : PowerSeries.constantCoeff l = 0`. Rewrite using `[← constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l ex h0, h1]`. Conclude with `MvPowerSeries.constantCoeff_X ()`.

Use `forall_mem_closure_of_isClosed_setOf T _ ?_ h3` and prove the remaining obligations. Use `isClosed_setOf_coeff_exp_norm_le_one _ _ ?_ ?_` and prove the remaining obligations. Introduce `e`. Simplify using `only [map_sub, MvPowerSeries.coeff_C_mul]`. Use `Continuous.sub ?_ ((continuous_fst.mul continuous_snd).mul continuous_const)` and prove the remaining obligations.

Conclude with `continuous_coeff_subst_subst_C_mul_subst l ex ph hl h0 _ continuous_fst e`. Introduce `n y`. Both sides reduce to the same expression.
-/
theorem phase_norm_limit_target : PI.PhNormLimit.Target := by
  unfold PI.PhNormLimit.Target
  intro p _ l ex ph T h0 h1 _ h3
  have hl : PowerSeries.constantCoeff l = 0 := by
    rw [← constantCoeff_subst_of_constantCoeff_eq_zero_orbital_bounds_conclusion l ex h0, h1]
    exact MvPowerSeries.constantCoeff_X ()
  refine forall_mem_closure_of_isClosed_setOf T _ ?_ h3
  refine isClosed_setOf_coeff_exp_norm_le_one _ _ ?_ ?_
  · intro e
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    refine Continuous.sub ?_ ((continuous_fst.mul continuous_snd).mul continuous_const)
    exact continuous_coeff_subst_subst_C_mul_subst l ex ph hl h0 _ continuous_fst e
  · intro n y
    rfl
