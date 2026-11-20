import Mathlib
import Formalism.GL3MeanSquares.LegendreCoefficient
import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector

noncomputable section

namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition

open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate

section Alg

variable {σ K : Type} [Field K] [Algebra ℚ K]

/- English proof (translation)
Use extensionality with `e`. Unfold `expS`. Rewrite using `[PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]`. Simplify using `only [PowerSeries.coeff_exp]`. Rewrite using `[← map_natCast (algebraMap ℚ K), ← map_mul, ← map_mul]`.

Use `congr 1`. Establish `h` using `Nat.add_choose_mul_factorial_mul_factorial (e 0) (e 1)`. Establish `h' : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) = ((e 0 + e 1).factorial : ℚ)`. Rewrite using `[Nat.choose_symm_add]`. Conclude with `h` after adjusting the coercions.

Establish `h0 : ((e 0).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Establish `h1 : ((e 1).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Establish `h2 : ((e 0 + e 1).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_biv :
    expS (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      expS (MvPowerSeries.X 0) * expS (MvPowerSeries.X 1) := by
  ext e
  unfold expS
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp]
  rw [← map_natCast (algebraMap ℚ K), ← map_mul, ← map_mul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial (e 0) (e 1)
  have h' : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    rw [Nat.choose_symm_add]; exact_mod_cast h
  have h0 : ((e 0).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h1 : ((e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h2 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  linarith

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst h` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hh`. Establish `ha : MvPowerSeries.HasSubst (fun _ : Unit => f)` using `PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hf)`. Unfold `expS`. Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha hs]`.
-/
theorem subst_expS {τ : Type} [Finite σ] (h : σ → MvPowerSeries τ K)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) (f : MvPowerSeries σ K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst h (expS f) = expS (MvPowerSeries.subst h f) := by
  have hs : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => f) :=
    PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hf)
  unfold expS
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha hs]

/- English proof (translation)
Set `h : Fin 2 → MvPowerSeries σ K` to `![f, g]`. Establish `hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0`. Introduce `i`. Use `fin_cases i`. Conclude with `hf`.

Conclude with `hg`. Establish `hS : MvPowerSeries.HasSubst h` using `by first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero hh`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hh`. Consider the case `exact ⟨fun s => by rw [hh s]; exact IsNilpotent.zero, by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩`.

Establish `e2 : ∀ i, MvPowerSeries.subst h (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = h i` using `fun i => MvPowerSeries.subst_X hS i`. Establish `e1 : MvPowerSeries.subst h (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = f + g`. Rewrite using `[MvPowerSeries.subst_add hS, e2, e2]`. Both sides reduce to the same expression. Establish `h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0` using `fun i => MvPowerSeries.constantCoeff_X i`.

Rewrite using `[← e1, ← subst_expS h hh _ (by rw [map_add, h0, h0, add_zero]), exp_biv, MvPowerSeries.subst_mul hS, subst_expS h hh _ (h0 0), subst_expS h hh _ (h0 1), e2, e2]`. Both sides reduce to the same expression.
-/
theorem expS_add (f g : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : expS (f + g) = expS f * expS g := by
  classical
  let h : Fin 2 → MvPowerSeries σ K := ![f, g]
  have hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0 := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have hS : MvPowerSeries.HasSubst h := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hh
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hh
    | exact ⟨fun s => by rw [hh s]; exact IsNilpotent.zero,
        by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have e2 : ∀ i, MvPowerSeries.subst h (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = h i :=
    fun i => MvPowerSeries.subst_X hS i
  have e1 : MvPowerSeries.subst h (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      f + g := by
    rw [MvPowerSeries.subst_add hS, e2, e2]
    rfl
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  rw [← e1, ← subst_expS h hh _ (by rw [map_add, h0, h0, add_zero]), exp_biv,
    MvPowerSeries.subst_mul hS, subst_expS h hh _ (h0 0), subst_expS h hh _ (h0 1), e2, e2]
  rfl

def Low (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

/- English proof (translation)
Introduce `d hd`. Rewrite using `[MvPowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p hp`. Use `replace hp : p.1 + p.2 = d := by first`.

Consider the case `exact _root_.Finset.mem_antidiagonal.1 hp`. Consider the case `exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Establish `hdeg : p.1.degree + p.2.degree = d.degree`. Rewrite using `[← hp]`. Use `first`.

Consider the case `exact (map_add Finsupp.degree p.1 p.2).symm`. Consider the case `exact (Finsupp.degree_add p.1 p.2).symm`. Consider the case `(rw [Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one]; exact (map_add _ _ _).symm)`. Consider the case `(simp only [Finsupp.degree]; exact (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm)`. Distinguish the cases in `h1 : p.1.degree < m`.

Rewrite using `[hx p.1 h1, zero_mul]`. Rewrite using `[hy p.2 (by omega), mul_zero]`.
-/
theorem Low.mul {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  replace hp : p.1 + p.2 = d := by
    first
    | exact _root_.Finset.mem_antidiagonal.1 hp
    | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp]
    first
    | exact (map_add Finsupp.degree p.1 p.2).symm
    | exact (Finsupp.degree_add p.1 p.2).symm
    | (rw [Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one,
        Finsupp.degree_eq_weight_one]; exact (map_add _ _ _).symm)
    | (simp only [Finsupp.degree]; exact (Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)).symm)
  by_cases h1 : p.1.degree < m
  · rw [hx p.1 h1, zero_mul]
  · rw [hy p.2 (by omega), mul_zero]

/- English proof (translation)
Introduce `d hd`. Establish `hd0 : d = 0`. Establish `h0 : d.degree = 0` using `by omega`. Use `first`. Consider the case `exact (Finsupp.degree_eq_zero_iff d).mp h0`.

Consider the case `exact Finsupp.degree_eq_zero_iff.mp h0`. Substitute `hd0` using the available equality. Use `first`. Consider the case `rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `hx`.

Consider the case `simpa using hx`.
-/
theorem low_one {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have hd0 : d = 0 := by
    have h0 : d.degree = 0 := by omega
    first
    | exact (Finsupp.degree_eq_zero_iff d).mp h0
    | exact Finsupp.degree_eq_zero_iff.mp h0
  subst hd0
  first
  | rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hx
  | simpa using hx

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro d hd`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul (low_one hx)`.
-/
theorem low_pow {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) (n : ℕ) :
    Low n (x ^ n) := by
  induction n with
  | zero => intro d hd; omega
  | succ n ih => rw [pow_succ]; exact ih.mul (low_one hx)

/- English proof (translation)
Unfold `expS`. Establish `ha : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Rewrite using `[PowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset _ (s := range N) ?_]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n _`.

Use `first`. Consider the case `rw [PowerSeries.coeff_exp, smul_eq_mul]`. Consider the case `simp [PowerSeries.coeff_exp]`. Introduce `n hn`. Rewrite `hn` using `[Function.mem_support]`.

Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hnN`. Use `push_neg at hnN`. Apply `hn` to reduce the goal to its premises. Rewrite using `[low_pow hf n d (by omega), smul_zero]`.
-/
theorem coeff_expS (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (d : σ →₀ ℕ) (N : ℕ) (hN : d.degree < N) :
    MvPowerSeries.coeff d (expS f) =
      ∑ n ∈ range N, algebraMap ℚ K (1 / n.factorial) * MvPowerSeries.coeff d (f ^ n) := by
  unfold expS
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset _ (s := range N) ?_]
  · apply Finset.sum_congr rfl
    intro n _
    first
    | rw [PowerSeries.coeff_exp, smul_eq_mul]
    | simp [PowerSeries.coeff_exp]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hnN
    push_neg at hnN
    apply hn
    rw [low_pow hf n d (by omega), smul_zero]

/- English proof (translation)
Unfold `expS`. Establish `ha : PowerSeries.HasSubst (0 : MvPowerSeries σ K)` using `PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)`. Use extensionality with `e`. Rewrite using `[PowerSeries.coeff_subst ha, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules.

Introduce `d hd`. Simplify using `[zero_pow hd]`.
-/
theorem expS_zero : expS (0 : MvPowerSeries σ K) = 1 := by
  unfold expS
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries σ K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  ext e
  rw [PowerSeries.coeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [zero_pow hd]

/- English proof (translation)
Unfold `expS`. Establish `ha : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Rewrite using `[PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`.

Simplify using `[hf, zero_pow hd]`.
-/
theorem constantCoeff_expS (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (expS f) = 1 := by
  unfold expS
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]

end Alg

section Normed

variable {σ K : Type} [NormedField K]

/- English proof (translation)
Establish `key : ∀ n, ∀ d : σ →₀ ℕ, d.degree = n → ‖MvPowerSeries.coeff d v‖ ≤ 1`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `d hd`.

Establish `hmul` using `congrArg (MvPowerSeries.coeff d) huv`. Rewrite `hmul` using `[MvPowerSeries.coeff_mul]`. Establish `hmem : ((0 : σ →₀ ℕ), d) ∈ Finset.HasAntidiagonal.antidiagonal d` using `Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add d)`. Rewrite `hmul` using `[← Finset.add_sum_erase _ _ hmem]`. Establish `hc : MvPowerSeries.coeff (0 : σ →₀ ℕ) u = 1` using `by first`.

Consider the case `rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `hu0`. Consider the case `simpa using hu0`. Simplify using `only [hc, one_mul] at hmul`. Rewrite using `[eq_sub_of_add_eq hmul]`.

Establish `hsub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖`. Introduce `a b`. Use `first`. Consider the case `(rw [sub_eq_add_neg]`. Establish `h1` using `IsUltrametricDist.norm_add_le_max a (-b)`.

Rewrite using `[norm_neg] at h1)` and apply the resulting hypothesis. Consider the case `(have h1 := IsUltrametricDist.dist_triangle_max a 0 b`. Simplify `h1)` using `[dist_eq_norm]`. Use `(hsub _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rw [MvPowerSeries.coeff_one] split_ifs <;> simp`.

Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_erase]`. Establish `hp2 : p.1 + p.2 = d` using `by first`. Consider the case `exact _root_.Finset.mem_antidiagonal.1 hp.2`.

Consider the case `exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp.2`. Establish `hp1 : p.1 ≠ 0`. Introduce `h0`. Apply `hp.1` to reduce the goal to its premises. Rewrite `hp2` using `[h0, zero_add]`.

Conclude with `Prod.ext h0 hp2`. Establish `hdeg : p.1.degree + p.2.degree = d.degree`. Rewrite using `[← hp2]`. Use `first`. Consider the case `exact (map_add Finsupp.degree p.1 p.2).symm`.

Consider the case `exact (Finsupp.degree_add p.1 p.2).symm`. Establish `hpos : 0 < p.1.degree`. Break down `Nat.eq_zero_or_pos p.1.degree with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hp1` to reduce the goal to its premises.

Use `first`. Consider the case `exact (Finsupp.degree_eq_zero_iff p.1).mp h`. Consider the case `exact Finsupp.degree_eq_zero_iff.mp h`. Conclude with `h`. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_mul (hu p.1) (ih p.2.degree (by omega) p.2 rfl) (norm_nonneg _) zero_le_one).trans (by norm_num)`. Introduce `d`. Conclude with `key _ d rfl`.
-/
theorem integral_of_mul_eq_one [IsUltrametricDist K] {u v : MvPowerSeries σ K} (huv : u * v = 1)
    (hu0 : MvPowerSeries.constantCoeff u = 1) (hu : IntegralMv u) : IntegralMv v := by
  classical
  have key : ∀ n, ∀ d : σ →₀ ℕ, d.degree = n → ‖MvPowerSeries.coeff d v‖ ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d hd
      have hmul := congrArg (MvPowerSeries.coeff d) huv
      rw [MvPowerSeries.coeff_mul] at hmul
      have hmem : ((0 : σ →₀ ℕ), d) ∈ Finset.HasAntidiagonal.antidiagonal d :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add d)
      rw [← Finset.add_sum_erase _ _ hmem] at hmul
      have hc : MvPowerSeries.coeff (0 : σ →₀ ℕ) u = 1 := by
        first
        | rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hu0
        | simpa using hu0
      simp only [hc, one_mul] at hmul
      rw [eq_sub_of_add_eq hmul]
      have hsub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
        intro a b
        first
        | (rw [sub_eq_add_neg]
           have h1 := IsUltrametricDist.norm_add_le_max a (-b)
           rwa [norm_neg] at h1)
        | (have h1 := IsUltrametricDist.dist_triangle_max a 0 b
           simpa [dist_eq_norm] using h1)
      refine (hsub _ _).trans (max_le ?_ ?_)
      · rw [MvPowerSeries.coeff_one]
        split_ifs <;> simp
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        intro p hp
        rw [Finset.mem_erase] at hp
        have hp2 : p.1 + p.2 = d := by
          first
          | exact _root_.Finset.mem_antidiagonal.1 hp.2
          | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp.2
        have hp1 : p.1 ≠ 0 := by
          intro h0
          apply hp.1
          rw [h0, zero_add] at hp2
          exact Prod.ext h0 hp2
        have hdeg : p.1.degree + p.2.degree = d.degree := by
          rw [← hp2]
          first
          | exact (map_add Finsupp.degree p.1 p.2).symm
          | exact (Finsupp.degree_add p.1 p.2).symm
        have hpos : 0 < p.1.degree := by
          rcases Nat.eq_zero_or_pos p.1.degree with h | h
          · exfalso
            apply hp1
            first
            | exact (Finsupp.degree_eq_zero_iff p.1).mp h
            | exact Finsupp.degree_eq_zero_iff.mp h
          · exact h
        rw [norm_mul]
        exact (mul_le_mul (hu p.1) (ih p.2.degree (by omega) p.2 rfl) (norm_nonneg _)
          zero_le_one).trans (by norm_num)
  intro d
  exact key _ d rfl

def CT (F : ℕ → MvPowerSeries σ K) (f : MvPowerSeries σ K) : Prop :=
  ∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (F k)) Filter.atTop
    (nhds (MvPowerSeries.coeff n f))

/- English proof (translation)
Introduce `n`. Simplify using `only [MvPowerSeries.coeff_mul]`. Apply `tendsto_finset_sum` to reduce the goal to its premises. Introduce `p _`. Conclude with `(hF p.1).mul (hG p.2)`.
-/
theorem CT.mul {F G : ℕ → MvPowerSeries σ K} {f g : MvPowerSeries σ K} (hF : CT F f)
    (hG : CT G g) : CT (fun k => F k * G k) (f * g) := by
  classical
  intro n
  simp only [MvPowerSeries.coeff_mul]
  apply tendsto_finset_sum
  intro p _
  exact (hF p.1).mul (hG p.2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `d`. Simplify using `only [pow_zero]`. Conclude with `tendsto_const_nhds`.

Consider the case `succ n ih`. Simplify using `only [pow_succ]`. Conclude with `ih.mul hF`.
-/
theorem CT.pow {F : ℕ → MvPowerSeries σ K} {f : MvPowerSeries σ K} (hF : CT F f) (n : ℕ) :
    CT (fun k => F k ^ n) (f ^ n) := by
  induction n with
  | zero =>
    intro d
    simp only [pow_zero]
    exact tendsto_const_nhds
  | succ n ih =>
    simp only [pow_succ]
    exact ih.mul hF

/- English proof (translation)
Use `⟨map_zero _, ?_⟩` and prove the remaining obligations. Rewrite using `[expS_zero]`. Introduce `d`. Rewrite using `[MvPowerSeries.coeff_one]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inLam_zero [IsUltrametricDist K] [Algebra ℚ K] : InLam (0 : MvPowerSeries σ K) := by
  refine ⟨map_zero _, ?_⟩
  classical
  rw [expS_zero]
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

/- English proof (translation)
Use `⟨by simp [hf.1, hg.1], ?_⟩` and prove the remaining obligations. Rewrite using `[expS_add f g hf.1 hg.1]`. Introduce `d`. Rewrite using `[MvPowerSeries.coeff_mul]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises.

Introduce `p _`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul (hf.2 p.1) (hg.2 p.2) (norm_nonneg _) zero_le_one).trans (by norm_num)`.
-/
theorem inLam_add [IsUltrametricDist K] [Algebra ℚ K] {f g : MvPowerSeries σ K} (hf : InLam f)
    (hg : InLam g) : InLam (f + g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  rw [expS_add f g hf.1 hg.1]
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  rw [norm_mul]
  exact (mul_le_mul (hf.2 p.1) (hg.2 p.2) (norm_nonneg _) zero_le_one).trans (by norm_num)

/- English proof (translation)
Use `⟨by simp [hf.1], ?_⟩` and prove the remaining obligations. Establish `h1 : expS f * expS (-f) = 1`. Rewrite using `[← expS_add f (-f) hf.1 (by simp [hf.1])]`. Use `first`. Consider the case `rw [add_neg_cancel, expS_zero]`.

Consider the case `rw [add_right_neg, expS_zero]`. Consider the case `simp [expS_zero]`. Conclude with `integral_of_mul_eq_one h1 (constantCoeff_expS f hf.1) hf.2`.
-/
theorem inLam_neg [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f) :
    InLam (-f) := by
  refine ⟨by simp [hf.1], ?_⟩
  have h1 : expS f * expS (-f) = 1 := by
    rw [← expS_add f (-f) hf.1 (by simp [hf.1])]
    first
    | rw [add_neg_cancel, expS_zero]
    | rw [add_right_neg, expS_zero]
    | simp [expS_zero]
  exact integral_of_mul_eq_one h1 (constantCoeff_expS f hf.1) hf.2

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using (inLam_zero : InLam (0 : MvPowerSeries σ K))`. Consider the case `succ m ih`. Rewrite using `[succ_nsmul]`. Conclude with `inLam_add ih hf`.
-/
theorem inLam_nsmul [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f)
    (m : ℕ) : InLam (m • f) := by
  induction m with
  | zero => simpa using (inLam_zero : InLam (0 : MvPowerSeries σ K))
  | succ m ih =>
    rw [succ_nsmul]
    exact inLam_add ih hf

end Normed

end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open ExpSeriesAddition

end Formalism.HermitianLattices.ExpSeriesBivariate
