import Mathlib
open SchwartzMap Filter Topology
open scoped Nat

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : HasFDerivAt (iteratedFDeriv ℝ j f) (fderiv ℝ (iteratedFDeriv ℝ j f) (t • x)) (t • x)` using `((hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)) (t • x)).hasFDerivAt`. Establish `h2 : HasDerivAt (fun s : ℝ => s • x) x t`. Simplify using `using (hasDerivAt_id t).smul_const x`. Establish `h3` using `h1.comp_hasDerivAt t h2`. Establish `h4` using `(ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => V) ℂ (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h3`.

Rewrite using `[iteratedFDeriv_succ_apply_left]`. Conclude with `h4`.
-/
theorem hasDerivAt_iteratedFDeriv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : V) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ j f (s • x) (fun _ => x))
      (iteratedFDeriv ℝ (j + 1) f (t • x) (fun _ => x)) t := by
  have h1 : HasFDerivAt (iteratedFDeriv ℝ j f) (fderiv ℝ (iteratedFDeriv ℝ j f) (t • x)) (t • x) :=
    ((hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)) (t • x)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have h3 := h1.comp_hasDerivAt t h2
  have h4 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => V) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h3
  rw [iteratedFDeriv_succ_apply_left]
  exact h4

/- English proof (translation)
The claim follows from `| 0 => by ext s; simp | j + 1 => by rw [iteratedDeriv_succ, iteratedDeriv_comp_line f hf x j] ext s exact (hasDerivAt_iteratedFDeriv_line f hf x j s).deriv`.
-/
theorem iteratedDeriv_comp_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : V) :
    ∀ j : ℕ, iteratedDeriv j (fun s : ℝ => f (s • x)) =
      fun s => iteratedFDeriv ℝ j f (s • x) (fun _ => x)
  | 0 => by ext s; simp
  | j + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_comp_line f hf x j]
    ext s
    exact (hasDerivAt_iteratedFDeriv_line f hf x j s).deriv

/- English proof (translation)
Introduce `V _ _ _ ψ A ρ hA x`. Use `set g : ℝ → ℂ := fun s => ψ (s • x) with hg`. Establish `hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ : V → ℂ)` using `ψ.smooth ⊤`. Establish `hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g` using `hψ.comp (contDiff_id.smul contDiff_const)`. Establish `hgn : ∀ n : ℕ, ContDiff ℝ n g` using `fun n => contDiff_infty.mp hgs n`.

Establish `hD` using `iteratedDeriv_comp_line (ψ : V → ℂ) hψ x`. Establish `hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1)` using `uniqueDiffOn_Icc zero_lt_one`. Establish `hT : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => x) = taylorWithinEval g m (Set.Icc 0 1) 0 1`. Introduce `m`. Rewrite using `[taylor_within_apply]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[iteratedDerivWithin_eq_iteratedDeriv hU (hgn j).contDiffAt (by simp), hD]`. Simplify using the standard rewrite rules. Use `set c : ℝ := |ρ| * ‖x‖ with hc`. Establish `hbound : ∀ m : ℕ, ‖g 1 - taylorWithinEval g m (Set.Icc 0 1) 0 1‖ ≤ |A| * c * (c ^ m / m !)`.

Introduce `m`. Establish `hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDerivWithin (m + 1) g (Set.Icc 0 1) y‖ ≤ |A| * c ^ (m + 1)`. Introduce `y hy`. Rewrite using `[iteratedDerivWithin_eq_iteratedDeriv hU (hgn (m + 1)).contDiffAt hy, hD]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `gcongr`. Use `(hA _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← abs_pow]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = |A| * c ^ (m + 1) := by rw [hc, mul_pow]; ring`. Establish `hcd : ContDiffOn ℝ (m + 1) g (Set.Icc 0 1)`. Conclude with `(hgn (m + 1)).contDiffOn` after adjusting the coercions. Use `taylor_mean_remainder_bound (n := m) (x := 1) zero_le_one hcd (by simp) hC` as an intermediate fact. Use `this.trans_eq ?_` and prove the remaining obligations.

Rewrite using `[sub_zero, one_pow, mul_one, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg1 : g 1 = ψ x` using `by simp [hg]`. Rewrite using `[← hg1]`. Repeatedly rewrite using `[hT]`.

Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Tendsto (fun m : ℕ => |A| * c * (c ^ m / m !)) atTop (𝓝 0)`. Simplify using `using (FloorSemiring.tendsto_pow_div_factorial_atTop c).const_mul (|A| * c)`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hlim` and prove the remaining obligations. Rewrite using `[norm_sub_rev]`.

Conclude with `hbound m`.
-/
theorem tendsto_taylor_sum_of_deriv_bound : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ x : V, Tendsto (fun m : ℕ => ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => x)) atTop (𝓝 (ψ x)) := by
  intro V _ _ _ ψ A ρ hA x
  set g : ℝ → ℂ := fun s => ψ (s • x) with hg
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ : V → ℂ) := ψ.smooth ⊤
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    hψ.comp (contDiff_id.smul contDiff_const)
  have hgn : ∀ n : ℕ, ContDiff ℝ n g := fun n => contDiff_infty.mp hgs n
  have hD := iteratedDeriv_comp_line (ψ : V → ℂ) hψ x
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hT : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => x) =
        taylorWithinEval g m (Set.Icc 0 1) 0 1 := by
    intro m
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hU (hgn j).contDiffAt (by simp), hD]
    simp
  set c : ℝ := |ρ| * ‖x‖ with hc
  have hbound : ∀ m : ℕ, ‖g 1 - taylorWithinEval g m (Set.Icc 0 1) 0 1‖ ≤
      |A| * c * (c ^ m / m !) := by
    intro m
    have hC : ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc 0 1) y‖ ≤ |A| * c ^ (m + 1) := by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv hU (hgn (m + 1)).contDiffAt hy, hD]
      calc ‖iteratedFDeriv ℝ (m + 1) ψ (y • x) (fun _ => x)‖
          ≤ ‖iteratedFDeriv ℝ (m + 1) ψ (y • x)‖ * ∏ _i : Fin (m + 1), ‖x‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ (|A| * |ρ| ^ (m + 1)) * ‖x‖ ^ (m + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            gcongr
            refine (hA _ _).trans ?_
            rw [← abs_pow]
            calc A * ρ ^ (m + 1) ≤ |A * ρ ^ (m + 1)| := le_abs_self _
              _ = |A| * |ρ ^ (m + 1)| := abs_mul _ _
        _ = |A| * c ^ (m + 1) := by rw [hc, mul_pow]; ring
    have hcd : ContDiffOn ℝ (m + 1) g (Set.Icc 0 1) := by
      exact_mod_cast (hgn (m + 1)).contDiffOn
    have := taylor_mean_remainder_bound (n := m) (x := 1) zero_le_one hcd (by simp) hC
    refine this.trans_eq ?_
    rw [sub_zero, one_pow, mul_one, pow_succ]
    ring
  have hg1 : g 1 = ψ x := by simp [hg]
  rw [← hg1]
  simp_rw [hT]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun m : ℕ => |A| * c * (c ^ m / m !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop c).const_mul (|A| * c)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hlim
  rw [norm_sub_rev]
  exact hbound m

end GlobalTheory
