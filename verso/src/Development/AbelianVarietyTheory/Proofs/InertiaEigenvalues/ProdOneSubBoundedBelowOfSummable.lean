import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Establish `hpos : 0 < 1 + 2 * s` using `by linarith`. Establish `h2 : 1 + 2 * s ≤ Real.exp (2 * s)` using `by linarith [Real.add_one_le_exp (2 * s)]`. Rewrite using `[Real.exp_neg]`. Establish `h3 : (Real.exp (2 * s))⁻¹ ≤ (1 + 2 * s)⁻¹` using `inv_anti₀ hpos h2`. Establish `h4 : (1 + 2 * s)⁻¹ ≤ 1 - s`.

Rewrite using `[inv_le_iff_one_le_mul₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_neg_two_mul_le_one_sub {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    Real.exp (-(2 * s)) ≤ 1 - s := by
  have hpos : 0 < 1 + 2 * s := by linarith
  have h2 : 1 + 2 * s ≤ Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
  rw [Real.exp_neg]
  have h3 : (Real.exp (2 * s))⁻¹ ≤ (1 + 2 * s)⁻¹ := inv_anti₀ hpos h2
  have h4 : (1 + 2 * s)⁻¹ ≤ 1 - s := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

/- English proof (translation)
Introduce `ι s h0 h1 hs`. Establish `hev : ∀ᶠ v in cofinite, s v < 1 / 2` using `hs.tendsto_cofinite_zero.eventually (eventually_lt_nhds (by norm_num))`. Establish `hfin : {v | ¬ s v < 1 / 2}.Finite` using `Filter.eventually_cofinite.mp hev`. Use `set F : Finset ι := hfin.toFinset with hFdef`. Establish `hout : ∀ v, v ∉ F → s v ≤ 1 / 2`.

Introduce `v hv`. Assume the negation of the conclusion as `hcon`. Conclude with `hv (by`. Rewrite using `[hFdef, Set.Finite.mem_toFinset]`. Introduce `hlt`.

Conclude with `hcon hlt.le)`. Establish `hfac : ∀ v, 0 < 1 - s v` using `fun v => by linarith [h1 v]`. Establish `hle1 : ∀ v, 1 - s v ≤ 1` using `fun v => by linarith [h0 v]`. Establish `hc : 0 < ∏ v ∈ F, (1 - s v)` using `Finset.prod_pos fun v _ => hfac v`. Use `⟨(∏ v ∈ F, (1 - s v)) * Real.exp (-(2 * ∑' v, s v)), mul_pos hc (Real.exp_pos _), fun S => ?_⟩` and prove the remaining obligations.

Establish `hsplit : ∏ v ∈ S, (1 - s v) = (∏ v ∈ S.filter (· ∈ F), (1 - s v)) * ∏ v ∈ S.filter (· ∉ F), (1 - s v)` using `(Finset.prod_filter_mul_prod_filter_not S (· ∈ F) _).symm`. Establish `hsub : S.filter (· ∈ F) ⊆ F` using `fun v hv => (Finset.mem_filter.mp hv).2`. Establish `hA : ∏ v ∈ F, (1 - s v) ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v)`. Rewrite using `[← Finset.prod_sdiff hsub]`. Establish `hp : 0 ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v)` using `Finset.prod_nonneg fun v _ => (hfac v).le`.

Establish `hq : ∏ v ∈ F \ S.filter (· ∈ F), (1 - s v) ≤ 1` using `Finset.prod_le_one (fun v _ => (hfac v).le) (fun v _ => hle1 v)`. Conclude with `mul_le_of_le_one_left hp hq`. Establish `hB : Real.exp (-(2 * ∑' v, s v)) ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v)`. Establish `hsum : ∑ v ∈ S.filter (· ∉ F), s v ≤ ∑' v, s v` using `hs.sum_le_tsum _ (fun v _ => h0 v)`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[Finset.sum_neg_distrib, ← Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ∏ v ∈ S.filter (· ∉ F), Real.exp (-(2 * s v)) := Real.exp_sum _ _`. Use `_ ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) := Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v hv => exp_neg_two_mul_le_one_sub (h0 v) (hout v (Finset.mem_filter.mp hv).2))`.

Rewrite using `[hsplit]`. Conclude with `mul_le_mul hA hB (Real.exp_pos _).le (Finset.prod_nonneg fun v _ => (hfac v).le)`.
-/
theorem prod_one_sub_bounded_below :
    ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s →
      ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  intro ι s h0 h1 hs
  classical
  have hev : ∀ᶠ v in cofinite, s v < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (eventually_lt_nhds (by norm_num))
  have hfin : {v | ¬ s v < 1 / 2}.Finite := Filter.eventually_cofinite.mp hev
  set F : Finset ι := hfin.toFinset with hFdef
  have hout : ∀ v, v ∉ F → s v ≤ 1 / 2 := by
    intro v hv
    by_contra hcon
    exact hv (by
      rw [hFdef, Set.Finite.mem_toFinset]
      intro hlt
      exact hcon hlt.le)
  have hfac : ∀ v, 0 < 1 - s v := fun v => by linarith [h1 v]
  have hle1 : ∀ v, 1 - s v ≤ 1 := fun v => by linarith [h0 v]
  have hc : 0 < ∏ v ∈ F, (1 - s v) := Finset.prod_pos fun v _ => hfac v
  refine ⟨(∏ v ∈ F, (1 - s v)) * Real.exp (-(2 * ∑' v, s v)), mul_pos hc (Real.exp_pos _),
    fun S => ?_⟩
  have hsplit : ∏ v ∈ S, (1 - s v) =
      (∏ v ∈ S.filter (· ∈ F), (1 - s v)) * ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ F) _).symm
  have hsub : S.filter (· ∈ F) ⊆ F := fun v hv => (Finset.mem_filter.mp hv).2
  have hA : ∏ v ∈ F, (1 - s v) ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) := by
    rw [← Finset.prod_sdiff hsub]
    have hp : 0 ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) :=
      Finset.prod_nonneg fun v _ => (hfac v).le
    have hq : ∏ v ∈ F \ S.filter (· ∈ F), (1 - s v) ≤ 1 :=
      Finset.prod_le_one (fun v _ => (hfac v).le) (fun v _ => hle1 v)
    exact mul_le_of_le_one_left hp hq
  have hB : Real.exp (-(2 * ∑' v, s v)) ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) := by
    have hsum : ∑ v ∈ S.filter (· ∉ F), s v ≤ ∑' v, s v :=
      hs.sum_le_tsum _ (fun v _ => h0 v)
    calc Real.exp (-(2 * ∑' v, s v))
        ≤ Real.exp (∑ v ∈ S.filter (· ∉ F), -(2 * s v)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ v ∈ S.filter (· ∉ F), Real.exp (-(2 * s v)) := Real.exp_sum _ _
      _ ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
          Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le)
            (fun v hv => exp_neg_two_mul_le_one_sub (h0 v)
              (hout v (Finset.mem_filter.mp hv).2))
  rw [hsplit]
  exact mul_le_mul hA hB (Real.exp_pos _).le
    (Finset.prod_nonneg fun v _ => (hfac v).le)

end GlobalTheory
