import Mathlib
import Formalism.EllipticTorsion.CompExpWeight

open PowerSeries IsUltrametricDist

universe u

namespace Formalism.ELL.MultiplicativeWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)

def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))

variable {c}

/- English proof (translation)
Introduce `e`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `only [norm_zero]`. Check the signs of the components of the expression.
-/
theorem W_one (hc : 0 < c) (_hc1 : c ≤ 1) : W c 0 (1 : MvPowerSeries σ K) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp only [norm_zero]; positivity

/- English proof (translation)
Introduce `e`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_` and prove the remaining obligations. Establish `hp : p.1 + p.2 = e` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← zpow_add₀ hc.ne', ← hp, map_add]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem W_mul (hc : 0 < c) {w₁ w₂ : ℤ} {f g : MvPowerSeries σ K} (hf : W c w₁ f) (hg : W c w₂ g) :
    W c (w₁ + w₂) (f * g) := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 f‖ * ‖MvPowerSeries.coeff p.2 g‖
      ≤ c ^ (w₁ - (p.1.degree : ℤ)) * c ^ (w₂ - (p.2.degree : ℤ)) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
    _ = c ^ (w₁ + w₂ - (e.degree : ℤ)) := by
        rw [← zpow_add₀ hc.ne', ← hp, map_add]; push_cast; ring_nf

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using W_one hc hc1`. Consider the case `succ n ih => rw [pow_succ]`. Use `push_cast`. Rewrite using `[add_mul, one_mul]`.

Conclude with `W_mul hc ih hf`.
-/
theorem W_pow (hc : 0 < c) (hc1 : c ≤ 1) {w : ℤ} {f : MvPowerSeries σ K} (hf : W c w f) (n : ℕ) :
    W c (n * w) (f ^ n) := by
  induction n with
  | zero => simpa using W_one hc hc1
  | succ n ih => rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact W_mul hc ih hf

/- English proof (translation)
Introduce `e`. Rewrite using `[PowerSeries.coeff_subst_single]`. Use `split_ifs with h`. Break down `Nat.eq_zero_or_pos (e i) with h0 | h0` into its components or cases. Rewrite using `[h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]`.

Check the signs of the components of the expression. Use `conv_rhs => rw [h, Finsupp.degree_single]`. Conclude with `hb _ h0`. Rewrite using `[norm_zero]`. Check the signs of the components of the expression.
-/
theorem W_E (E : PowerSeries K) (hE : constantCoeff E = 0)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) (hc : 0 < c) (i : σ) :
    W c 1 (E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE, norm_zero]; positivity
    · conv_rhs => rw [h, Finsupp.degree_single]
      exact hb _ h0
  · rw [norm_zero]; positivity

/- English proof (translation)
Unfold `Finsupp.prod`. Establish `hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ)` using `by show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _ push_cast; rfl`. Rewrite using `[hdeg]`. Proceed by induction on `d.support using Finset.induction_on with`. Consider the case `empty => simpa using W_one hc hc1`.

Consider the case `insert s S hs ih`. Rewrite using `[Finset.prod_insert hs, Finset.sum_insert hs]`. Use `W_pow hc hc1 (ha s) (d s)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `W_mul hc this ih`.
-/
theorem W_prod (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih

/- English proof (translation)
Introduce `K _ _ σ _ c hc hc1 E hE hb G hG α`. Establish `ha` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K) (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE`. Rewrite using `[MvPowerSeries.coeff_subst ha]`. Establish `hfin` using `MvPowerSeries.coeff_subst_finite ha G α`. Rewrite using `[finsum_eq_sum _ hfin]`.

Use `norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, norm_mul]`. Establish `h1` using `W_prod hc hc1 _ (W_E E hE hb hc) d α`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)`.
-/
theorem comp_exp_coeff_weight_of : CompExpWeight.{u} := by
  intro K _ _ σ _ c hc hc1 E hE hb G hG α
  classical
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := σ) (S := K)
    (a := fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K))
    fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE
  rw [MvPowerSeries.coeff_subst ha]
  have hfin := MvPowerSeries.coeff_subst_finite ha G α
  rw [finsum_eq_sum _ hfin]
  refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun d _ => ?_
  rw [smul_eq_mul, norm_mul]
  have h1 := W_prod hc hc1 _ (W_E E hE hb hc) d α
  calc ‖MvPowerSeries.coeff d G‖ * ‖MvPowerSeries.coeff α
          (d.prod fun s e => (E.subst (MvPowerSeries.X s : MvPowerSeries σ K)) ^ e)‖
      ≤ 1 * c ^ ((d.degree : ℤ) - (α.degree : ℤ)) :=
        mul_le_mul (hG d) h1 (norm_nonneg _) zero_le_one
    _ ≤ c ^ (-(α.degree : ℤ)) := by
        rw [one_mul]; exact zpow_le_zpow_right_of_le_one₀ hc hc1 (by omega)

end Formalism.ELL.MultiplicativeWeight

namespace Formalism.ELL

/- English proof (translation)
The claim follows from `Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of`.
-/
theorem comp_exp_coeff_weight : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of

end Formalism.ELL
