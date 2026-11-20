import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ExteriorInterpolation

/- English proof (translation)
Take `⟨P, hP⟩ : ∃ P : Polynomial ℂ, P = ∏ i, (Polynomial.X + Polynomial.C (-z i))` from `⟨_, rfl⟩`. Use `⟨fun k => P.coeff k, fun w => ?_, ?_⟩` and prove the remaining obligations. Establish `hdeg : P.natDegree < l + 1`. Establish `h1` using `Polynomial.natDegree_prod_le (s := Finset.univ) (f := fun i => Polynomial.X + Polynomial.C (-z i))`. Simplify using `only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1`.

Rewrite using `[hP]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Polynomial.eval_eq_sum_range' hdeg, hP, Polynomial.eval_prod]`. Simplify using `[sub_eq_add_neg]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k hk`. Establish `hk' : k ≤ (Finset.univ : Finset (Fin l)).card`. Simplify `hk` using `[Nat.lt_succ_iff]`. Rewrite using `[hP, Finset.prod_X_add_C_coeff _ _ hk']`.

Combine the equalities or inequalities in the displayed calculation. Apply `norm_sum_le_of_le` to reduce the goal to its premises. Introduce `t _`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by rw [norm_neg]; exact hz i)`.

Use `_ = ((l.choose (l - k) : ℕ) : ℝ) := by`. Simplify using `[Finset.card_powersetCard, Finset.card_univ]`. Use `_ = ∑ k ∈ Finset.range (l + 1), ((l.choose k : ℕ) : ℝ) := by`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k hk`.

Rewrite using `[Nat.choose_symm (by simpa [Nat.lt_succ_iff] using hk)]`. Use `_ = 2 ^ l := by exact_mod_cast Nat.sum_range_choose l`.
-/
theorem exists_coeffs (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ a : ℕ → ℂ, (∀ w : ℂ, ∏ i, (w - z i) = ∑ k ∈ Finset.range (l + 1), a k * w ^ k) ∧
      ∑ k ∈ Finset.range (l + 1), ‖a k‖ ≤ 2 ^ l := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, P = ∏ i, (Polynomial.X + Polynomial.C (-z i)) := ⟨_, rfl⟩
  refine ⟨fun k => P.coeff k, fun w => ?_, ?_⟩
  · have hdeg : P.natDegree < l + 1 := by
      have h1 := Polynomial.natDegree_prod_le (s := Finset.univ)
        (f := fun i => Polynomial.X + Polynomial.C (-z i))
      simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] at h1
      rw [hP]
      omega
    rw [← Polynomial.eval_eq_sum_range' hdeg, hP, Polynomial.eval_prod]
    simp [sub_eq_add_neg]
  · calc ∑ k ∈ Finset.range (l + 1), ‖P.coeff k‖
          ≤ ∑ k ∈ Finset.range (l + 1), ((l.choose (l - k) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ (Finset.univ : Finset (Fin l)).card := by
            simpa [Nat.lt_succ_iff] using hk
          rw [hP, Finset.prod_X_add_C_coeff _ _ hk']
          calc ‖∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), ∏ i ∈ t, -z i‖
              ≤ ∑ t ∈ (Finset.univ : Finset (Fin l)).powersetCard
                  ((Finset.univ : Finset (Fin l)).card - k), (1 : ℝ) := by
                apply norm_sum_le_of_le
                intro t _
                rw [norm_prod]
                exact Finset.prod_le_one (fun i _ => norm_nonneg _)
                  (fun i _ => by rw [norm_neg]; exact hz i)
            _ = ((l.choose (l - k) : ℕ) : ℝ) := by
                simp [Finset.card_powersetCard, Finset.card_univ]
      _ = ∑ k ∈ Finset.range (l + 1), ((l.choose k : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.choose_symm (by simpa [Nat.lt_succ_iff] using hk)]
      _ = 2 ^ l := by exact_mod_cast Nat.sum_range_choose l

/- English proof (translation)
Take `⟨a, ha, hsum⟩` from `exists_coeffs l z hz`. Use `⟨fun j ζ => ∑ k ∈ Finset.range (l + 1), if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Apply the tactic sequence `exact continuous_finsetSum _ (fun k _ => by split_ifs <;> fun_prop)`. Introduce `j ζ hζ`.

Combine the equalities or inequalities in the displayed calculation. Apply `norm_sum_le_of_le` to reduce the goal to its premises. Introduce `k _`. Use `split_ifs`. Rewrite using `[norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hζ)`. Simplify using the standard rewrite rules. Use `_ ≤ 2 ^ l := hsum`. Introduce `ζ w`. Rewrite using `[ha ζ, ha w, ← Finset.sum_sub_distrib]`.

Establish `e1 : (∑ j : Fin l, (∑ k ∈ Finset.range (l + 1), if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ (j : ℕ)) = ∑ k ∈ Finset.range (l + 1), ∑ j ∈ Finset.range l, (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range (l + 1), if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j) l]`. Repeatedly rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Rewrite using `[e1, Finset.sum_mul]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k hk`. Establish `hkl : k ≤ l` using `by simpa [Nat.lt_succ_iff] using hk`. Establish `e2 : ∑ j ∈ Finset.range l, (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j = a k * ∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j)`. Rewrite using `[Finset.mul_sum, show Finset.range k = (Finset.range l).filter (· < k) by ext j; simp; omega, Finset.sum_filter]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Apply the tactic sequence `split_ifs <;> ring`. Establish `e3 : (∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j)) * (ζ - w) = ζ ^ k - w ^ k`. Rewrite using `[← neg_sub w ζ, mul_neg, geom_sum₂_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, mul_assoc, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_divided (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ b : Fin l → ℂ → ℂ, (∀ j, Continuous (b j)) ∧ (∀ j ζ, ‖ζ‖ ≤ 1 → ‖b j ζ‖ ≤ 2 ^ l) ∧
      ∀ ζ w : ℂ, (∑ j, b j ζ * w ^ (j : ℕ)) * (ζ - w) = ∏ i, (ζ - z i) - ∏ i, (w - z i) := by
  obtain ⟨a, ha, hsum⟩ := exists_coeffs l z hz
  refine ⟨fun j ζ => ∑ k ∈ Finset.range (l + 1),
    if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0, ?_, ?_, ?_⟩
  · intro j
    exact continuous_finsetSum _ (fun k _ => by split_ifs <;> fun_prop)
  · intro j ζ hζ
    calc ‖∑ k ∈ Finset.range (l + 1), if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0‖
        ≤ ∑ k ∈ Finset.range (l + 1), ‖a k‖ := by
          apply norm_sum_le_of_le
          intro k _
          split_ifs
          · rw [norm_mul, norm_pow]
            exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hζ)
          · simp
      _ ≤ 2 ^ l := hsum
  · intro ζ w
    rw [ha ζ, ha w, ← Finset.sum_sub_distrib]
    have e1 : (∑ j : Fin l, (∑ k ∈ Finset.range (l + 1),
          if (j : ℕ) < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ (j : ℕ))
        = ∑ k ∈ Finset.range (l + 1), ∑ j ∈ Finset.range l,
          (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (∑ k ∈ Finset.range (l + 1),
        if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j) l]
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [e1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkl : k ≤ l := by simpa [Nat.lt_succ_iff] using hk
    have e2 : ∑ j ∈ Finset.range l, (if j < k then a k * ζ ^ (k - 1 - j) else 0) * w ^ j
        = a k * ∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j) := by
      rw [Finset.mul_sum,
        show Finset.range k = (Finset.range l).filter (· < k) by ext j; simp; omega,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    have e3 : (∑ j ∈ Finset.range k, w ^ j * ζ ^ (k - 1 - j)) * (ζ - w) = ζ ^ k - w ^ k := by
      rw [← neg_sub w ζ, mul_neg, geom_sum₂_mul]
      ring
    rw [e2, mul_assoc, e3]
    ring

/- English proof (translation)
Establish `hS : {ζ : ℂ | r ≤ ‖ζ‖} ∈ 𝓝 w` using `Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hw) (fun ζ hζ => by simp only [Set.mem_ofPred_eq] at hζ ⊢; exact hζ.le)`. Establish `hgw : DifferentiableAt ℂ g w` using `hg.differentiableAt hS`. Take `⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = dslope g w` from `⟨_, rfl⟩`. Establish `hFc : ContinuousOn F {ζ : ℂ | r ≤ ‖ζ‖}`. Rewrite using `[hF]`.

Conclude with `(continuousOn_dslope hS).mpr ⟨hg.continuousOn, hgw⟩`. Establish `main : ∀ R : ℝ, ‖w‖ < R → (∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ) = (∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ) - 2 * Real.pi * I * g w`. Introduce `R hR`. Establish `hrR : r ≤ R` using `(hw.trans hR).le`. Establish `hsub : ∀ ρ, r ≤ ρ → Metric.sphere (0 : ℂ) ρ ⊆ {ζ : ℂ | r ≤ ‖ζ‖}`.

Introduce `ρ h1 ζ hζ`. Rewrite `hζ` using `[mem_sphere_zero_iff_norm]`. Use `show r ≤ ‖ζ‖`. Rewrite using `[hζ]`. Conclude with `h1`.

Establish `split : ∀ ρ, r ≤ ρ → ‖w‖ ≠ ρ → (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * g ζ) = g w * (∮ ζ in C(0, ρ), (ζ - w)⁻¹) + ∮ ζ in C(0, ρ), F ζ`. Introduce `ρ h1 hne`. Establish `hρ : 0 ≤ ρ` using `hr.le.trans h1`. Establish `hne' : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ - w ≠ 0`. Introduce `ζ hζ h`.

Rewrite `hζ` using `[mem_sphere_zero_iff_norm]`. Rewrite `h` using `[sub_eq_zero]`. Rewrite `hζ` using `[h]`. Conclude with `hne hζ`. Establish `c1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.sphere (0 : ℂ) ρ)` using `(continuousOn_id.sub continuousOn_const).inv₀ hne'`.

Rewrite using `[← smul_eq_mul (g w), ← circleIntegral.integral_smul (g w) _ 0 ρ, ← circleIntegral.integral_add (show CircleIntegrable (fun ζ => g w • (ζ - w)⁻¹) 0 ρ from (ContinuousOn.circleIntegrable hρ (by fun_prop (disch := exact hne')))) ((hFc.mono (hsub ρ h1)).circleIntegrable hρ)]`. Apply `circleIntegral.integral_congr hρ` to reduce the goal to its premises. Introduce `ζ hζ`. Establish `hz` using `hne' ζ hζ`. Simplify using `only [hF, dslope_of_ne _ (sub_ne_zero.mp hz), slope_def_field, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hann : (∮ ζ in C(0, R), F ζ) = ∮ ζ in C(0, r), F ζ`. Apply `circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR (Set.countable_singleton w)` to reduce the goal to its premises. Use `hFc.mono ?_` and prove the remaining obligations.

Introduce `ζ hζ`. Use `hζ.2` as an intermediate fact. Rewrite `this` using `[Metric.mem_ball, dist_zero_right, not_lt]`. Conclude with `this`. Introduce `ζ hζ`.

Establish `hζ1` using `hζ.1.2`. Rewrite `hζ1` using `[Metric.mem_closedBall, dist_zero_right, not_le]`. Establish `hζw : ζ ≠ w` using `hζ.2`. Rewrite using `[hF, differentiableAt_dslope_of_ne hζw]`. Conclude with `hg.differentiableAt (Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hζ1) (fun x hx => by simp only [Set.mem_ofPred_eq] at hx ⊢; exact hx.le))`.

Establish `hzero : (∮ ζ in C(0, r), (ζ - w)⁻¹) = 0`. Establish `hne0 : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ζ - w ≠ 0`. Introduce `ζ hζ h`. Rewrite `hζ` using `[Metric.mem_closedBall, dist_zero_right]`. Rewrite `h` using `[sub_eq_zero]`.

Rewrite `hζ` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty` to reduce the goal to its premises. Conclude with `(continuousOn_id.sub continuousOn_const).inv₀ hne0`. Introduce `ζ hζ`.

Conclude with `(differentiableAt_id.sub_const w).inv (hne0 ζ (Metric.ball_subset_closedBall hζ.1))`. Establish `hone : (∮ ζ in C(0, R), (ζ - w)⁻¹) = 2 * Real.pi * I` using `circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR)`. Rewrite using `[split r le_rfl (ne_of_gt hw), split R hrR (ne_of_lt hR), hann, hzero, hone]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨S, hS'⟩ : ∃ S, S = ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ` from `⟨_, rfl⟩`.

Rewrite using `[← hS']`. Establish `hK : ∀ ε > 0, ‖S + 2 * Real.pi * I * g w‖ ≤ 4 * Real.pi * ε`. Introduce `ε hε`. Establish `hev : ∀ᶠ ζ in cocompact ℂ, ‖g ζ‖ ≤ ε` using `by filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hε)] with ζ hζ`. Simplify using `using hζ`.

Take `⟨K, hKc, hKs⟩` from `(Filter.hasBasis_cocompact.eventually_iff).mp hev`. Take `⟨M, hM⟩` from `hKc.isBounded.subset_closedBall 0`. Use `set R : ℝ := max (M + 1) (2 * ‖w‖ + 1) with hRdef`. Establish `hR1 : M + 1 ≤ R` using `le_max_left _ _`. Establish `hR2 : 2 * ‖w‖ + 1 ≤ R` using `le_max_right _ _`.

Establish `hRpos : 0 < R` using `by linarith [norm_nonneg w]`. Establish `hwR : ‖w‖ < R` using `by linarith [norm_nonneg w]`. Rewrite using `[hS', main R hwR]`. Simplify using `only [sub_add_cancel]`. Establish `hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖(ζ - w)⁻¹ * g ζ‖ ≤ 2 / R * ε`.

Introduce `ζ hζ`. Rewrite `hζ` using `[mem_sphere_zero_iff_norm]`. Establish `hgz : ‖g ζ‖ ≤ ε`. Apply `hKs` to reduce the goal to its premises. Introduce `hK'`.

Use `hM hK'` as an intermediate fact. Rewrite `this` using `[Metric.mem_closedBall, dist_zero_right]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : R / 2 ≤ ‖ζ - w‖`. Use `norm_sub_norm_le ζ w` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinv : ‖ζ - w‖⁻¹ ≤ 2 / R`. Rewrite using `[show 2 / R = (R / 2)⁻¹ by field_simp]`. Conclude with `inv_anti₀ (by positivity) hd`. Rewrite using `[norm_mul, norm_inv]`.

Conclude with `mul_le_mul hinv hgz (norm_nonneg _) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Establish `h00 : ‖S + 2 * Real.pi * I * g w‖ = 0`. Apply `le_antisymm _ (norm_nonneg _)` to reduce the goal to its premises. Assume the negation of the conclusion as `hpos'`.

Establish `hpos` using `lt_of_not_ge hpos'`. Establish `h8` using `hK (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi)) (by positivity)`. Establish `: 4 * Real.pi * (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi)) = ‖S + 2 * Real.pi * I * g w‖ / 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h8` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `norm_eq_zero.mp h00` as an intermediate fact. Take the linear combination `this`.
-/
theorem cauchy_exterior (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hg : DifferentiableOn ℂ g {w | r ≤ ‖w‖}) (h0 : Tendsto g (Filter.cocompact ℂ) (𝓝 0))
    (w : ℂ) (hw : r < ‖w‖) :
    ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ = -(2 * Real.pi * I * g w) := by
  have hS : {ζ : ℂ | r ≤ ‖ζ‖} ∈ 𝓝 w :=
    Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hw)
      (fun ζ hζ => by simp only [Set.mem_ofPred_eq] at hζ ⊢; exact hζ.le)
  have hgw : DifferentiableAt ℂ g w := hg.differentiableAt hS
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = dslope g w := ⟨_, rfl⟩
  have hFc : ContinuousOn F {ζ : ℂ | r ≤ ‖ζ‖} := by
    rw [hF]
    exact (continuousOn_dslope hS).mpr ⟨hg.continuousOn, hgw⟩
  have main : ∀ R : ℝ, ‖w‖ < R → (∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ)
      = (∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ) - 2 * Real.pi * I * g w := by
    intro R hR
    have hrR : r ≤ R := (hw.trans hR).le
    have hsub : ∀ ρ, r ≤ ρ → Metric.sphere (0 : ℂ) ρ ⊆ {ζ : ℂ | r ≤ ‖ζ‖} := by
      intro ρ h1 ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      show r ≤ ‖ζ‖
      rw [hζ]
      exact h1
    have split : ∀ ρ, r ≤ ρ → ‖w‖ ≠ ρ → (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * g ζ)
        = g w * (∮ ζ in C(0, ρ), (ζ - w)⁻¹) + ∮ ζ in C(0, ρ), F ζ := by
      intro ρ h1 hne
      have hρ : 0 ≤ ρ := hr.le.trans h1
      have hne' : ∀ ζ ∈ Metric.sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [mem_sphere_zero_iff_norm] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        exact hne hζ
      have c1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
        (continuousOn_id.sub continuousOn_const).inv₀ hne'
      rw [← smul_eq_mul (g w), ← circleIntegral.integral_smul (g w) _ 0 ρ,
        ← circleIntegral.integral_add
          (show CircleIntegrable (fun ζ => g w • (ζ - w)⁻¹) 0 ρ from
            (ContinuousOn.circleIntegrable hρ (by fun_prop (disch := exact hne'))))
          ((hFc.mono (hsub ρ h1)).circleIntegrable hρ)]
      apply circleIntegral.integral_congr hρ
      intro ζ hζ
      have hz := hne' ζ hζ
      simp only [hF, dslope_of_ne _ (sub_ne_zero.mp hz), slope_def_field, smul_eq_mul]
      field_simp
      ring
    have hann : (∮ ζ in C(0, R), F ζ) = ∮ ζ in C(0, r), F ζ := by
      apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
        (Set.countable_singleton w)
      · refine hFc.mono ?_
        intro ζ hζ
        have := hζ.2
        rw [Metric.mem_ball, dist_zero_right, not_lt] at this
        exact this
      · intro ζ hζ
        have hζ1 := hζ.1.2
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hζ1
        have hζw : ζ ≠ w := hζ.2
        rw [hF, differentiableAt_dslope_of_ne hζw]
        exact hg.differentiableAt
          (Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hζ1)
            (fun x hx => by simp only [Set.mem_ofPred_eq] at hx ⊢; exact hx.le))
    have hzero : (∮ ζ in C(0, r), (ζ - w)⁻¹) = 0 := by
      have hne0 : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, ζ - w ≠ 0 := by
        intro ζ hζ h
        rw [Metric.mem_closedBall, dist_zero_right] at hζ
        rw [sub_eq_zero] at h
        rw [h] at hζ
        linarith
      apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      · exact (continuousOn_id.sub continuousOn_const).inv₀ hne0
      · intro ζ hζ
        exact (differentiableAt_id.sub_const w).inv
          (hne0 ζ (Metric.ball_subset_closedBall hζ.1))
    have hone : (∮ ζ in C(0, R), (ζ - w)⁻¹) = 2 * Real.pi * I :=
      circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR)
    rw [split r le_rfl (ne_of_gt hw), split R hrR (ne_of_lt hR), hann, hzero, hone]
    ring
  obtain ⟨S, hS'⟩ : ∃ S, S = ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ := ⟨_, rfl⟩
  rw [← hS']
  have hK : ∀ ε > 0, ‖S + 2 * Real.pi * I * g w‖ ≤ 4 * Real.pi * ε := by
    intro ε hε
    have hev : ∀ᶠ ζ in cocompact ℂ, ‖g ζ‖ ≤ ε := by
      filter_upwards [h0 (Metric.closedBall_mem_nhds 0 hε)] with ζ hζ
      simpa using hζ
    obtain ⟨K, hKc, hKs⟩ := (Filter.hasBasis_cocompact.eventually_iff).mp hev
    obtain ⟨M, hM⟩ := hKc.isBounded.subset_closedBall 0
    set R : ℝ := max (M + 1) (2 * ‖w‖ + 1) with hRdef
    have hR1 : M + 1 ≤ R := le_max_left _ _
    have hR2 : 2 * ‖w‖ + 1 ≤ R := le_max_right _ _
    have hRpos : 0 < R := by linarith [norm_nonneg w]
    have hwR : ‖w‖ < R := by linarith [norm_nonneg w]
    rw [hS', main R hwR]
    simp only [sub_add_cancel]
    have hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖(ζ - w)⁻¹ * g ζ‖ ≤ 2 / R * ε := by
      intro ζ hζ
      rw [mem_sphere_zero_iff_norm] at hζ
      have hgz : ‖g ζ‖ ≤ ε := by
        apply hKs
        intro hK'
        have := hM hK'
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith
      have hd : R / 2 ≤ ‖ζ - w‖ := by
        have := norm_sub_norm_le ζ w
        linarith
      have hinv : ‖ζ - w‖⁻¹ ≤ 2 / R := by
        rw [show 2 / R = (R / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) hd
      rw [norm_mul, norm_inv]
      exact mul_le_mul hinv hgz (norm_nonneg _) (by positivity)
    calc ‖∮ ζ in C(0, R), (ζ - w)⁻¹ * g ζ‖ ≤ 2 * Real.pi * R * (2 / R * ε) :=
          circleIntegral.norm_integral_le_of_norm_le_const hRpos.le hb
      _ = 4 * Real.pi * ε := by field_simp; ring
  have h00 : ‖S + 2 * Real.pi * I * g w‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos'
    have hpos := lt_of_not_ge hpos'
    have h8 := hK (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi)) (by positivity)
    have : 4 * Real.pi * (‖S + 2 * Real.pi * I * g w‖ / (8 * Real.pi))
        = ‖S + 2 * Real.pi * I * g w‖ / 2 := by
      field_simp
      ring
    rw [this] at h8
    linarith
  have := norm_eq_zero.mp h00
  linear_combination this

/- English proof (translation)
Simplify using `only [circleIntegral, Finset.smul_sum]`. Conclude with `intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).out)`.
-/
private theorem circleIntegral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).out)

/- English proof (translation)
Introduce `l z g r G hr hr1 hz hg h0 hG`. Take `⟨b, hbc, hbb, hbid⟩` from `exists_divided l z (fun i => (hz i).2)`. Establish `hPne : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ∏ k, (ζ - z k) ≠ 0`. Introduce `ζ hζ`. Rewrite using `[Finset.prod_ne_zero_iff]`.

Introduce `k _ h`. Rewrite `hζ` using `[mem_sphere_zero_iff_norm]`. Rewrite `h` using `[sub_eq_zero]`. Use `(hz k).1` as an intermediate fact. Rewrite `this` using `[← h, hζ]`.

Conclude with `lt_irrefl _ this`. Establish `hsph : Metric.sphere (0 : ℂ) r ⊆ {w : ℂ | r ≤ ‖w‖}`. Introduce `ζ hζ`. Rewrite `hζ` using `[mem_sphere_zero_iff_norm]`. Use `show r ≤ ‖ζ‖`.

Rewrite using `[hζ]`. Establish `hcont : ∀ j, ContinuousOn (fun ζ => g ζ / (∏ k, (ζ - z k)) * b j ζ) (Metric.sphere (0 : ℂ) r)`. Introduce `j`. Use `ContinuousOn.mul ?_ (hbc j).continuousOn` and prove the remaining obligations. Conclude with `(hg.continuousOn.mono hsph).div (by fun_prop) hPne`.

Take `⟨c, hc⟩ : ∃ c : Fin l → ℂ, c = fun j => -(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ` from `⟨_, rfl⟩`. Establish `hpi : (2 * (Real.pi : ℂ) * I) ≠ 0`. Simplify using `[Real.pi_ne_zero, I_ne_zero]`. Use `⟨c, fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `hwi` using `(hz i).1`.

Establish `e1 : ∑ j, c j * z i ^ (j : ℕ) = -(2 * (Real.pi : ℂ) * I)⁻¹ * ∑ j : Fin l, ∮ ζ in C(0, r), z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ)`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[circleIntegral.integral_smul, hc, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, ← circleIntegral_finset_sum' Finset.univ (fun (j : Fin l) ζ => z i ^ (j : ℕ) • ((g ζ / ∏ k, (ζ - z k)) * b j ζ)) 0 r (fun j _ => ContinuousOn.circleIntegrable hr.le ((hcont j).const_smul (z i ^ (j : ℕ))))]`. Establish `e2 : (∮ ζ in C(0, r), ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ)) = ∮ ζ in C(0, r), (ζ - z i)⁻¹ * g ζ`. Apply `circleIntegral.integral_congr hr.le` to reduce the goal to its premises. Introduce `ζ hζ`.

Establish `hPζ` using `hPne ζ hζ`. Establish `hzne : ζ - z i ≠ 0`. Introduce `h`. Rewrite `h` using `[sub_eq_zero]`. Rewrite `hζ` using `[mem_sphere_zero_iff_norm, h]`.

Rewrite `hwi` using `[hζ]`. Conclude with `lt_irrefl _ hwi`. Establish `e` using `hbid ζ (z i)`. Establish `hPz : ∏ k, (z i - z k) = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)`. Rewrite `e` using `[hPz, sub_zero]`.

Establish `hsum : ∑ j, b j ζ * z i ^ (j : ℕ) = (∏ k, (ζ - z k)) / (ζ - z i)` using `eq_div_of_mul_eq hzne e`. Establish `e3 : ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ) = g ζ / (∏ k, (ζ - z k)) * ∑ j, b j ζ * z i ^ (j : ℕ)`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[e3, hsum]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2, cauchy_exterior g r hr hg h0 (z i) hwi]`. Clear the denominators using the available nonvanishing facts. Establish `hsph1 : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖ζ‖ = r` using `fun ζ hζ => mem_sphere_zero_iff_norm.mp hζ`. Establish `hG0 : 0 ≤ G`. Establish `hmem : ((r : ℂ)) ∈ Metric.sphere (0 : ℂ) r`.

Rewrite using `[mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]`. Establish `hpos : 0 < ‖∏ k, ((r : ℂ) - z k)‖` using `norm_pos_iff.mpr (hPne _ hmem)`. Establish `h1` using `hG (r : ℂ) (hsph1 _ hmem)`. Assume the negation of the conclusion as `hneg`. Establish `hlt : G * ‖∏ k, ((r : ℂ) - z k)‖ < 0` using `mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos`.

Combine the linear relations using `[norm_nonneg (g (r : ℂ))]`. Establish `hbound : ∀ j, ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖g ζ / (∏ k, (ζ - z k)) * b j ζ‖ ≤ G * 2 ^ l`. Introduce `j ζ hζ`. Establish `hpos : 0 < ‖∏ k, (ζ - z k)‖` using `norm_pos_iff.mpr (hPne ζ hζ)`. Establish `hq : ‖g ζ‖ / ‖∏ k, (ζ - z k)‖ ≤ G`.

Rewrite using `[div_le_iff₀ hpos]`. Conclude with `hG ζ (hsph1 ζ hζ)`. Establish `hb` using `hbb j ζ (by rw [hsph1 ζ hζ]; exact hr1)`. Rewrite using `[norm_mul, norm_div]`. Conclude with `mul_le_mul hq hb (norm_nonneg _) hG0`.

Establish `hcj : ∀ j, ‖c j‖ ≤ 2 ^ l * (r * G)`. Introduce `j`. Establish `hI` using `circleIntegral.norm_integral_le_of_norm_le_const hr.le (hbound j)`. Establish `hn : ‖-(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹`. Rewrite using `[norm_neg, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]`.

Evaluate the numerical expressions. Rewrite using `[hc]`. Simplify using `only`. Rewrite using `[norm_mul, hn]`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Establish `hl : (l : ℝ) ≤ 2 ^ l` using `by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interpolation : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  intro l z g r G hr hr1 hz hg h0 hG
  obtain ⟨b, hbc, hbb, hbid⟩ := exists_divided l z (fun i => (hz i).2)
  have hPne : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ∏ k, (ζ - z k) ≠ 0 := by
    intro ζ hζ
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [sub_eq_zero] at h
    have := (hz k).1
    rw [← h, hζ] at this
    exact lt_irrefl _ this
  have hsph : Metric.sphere (0 : ℂ) r ⊆ {w : ℂ | r ≤ ‖w‖} := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    show r ≤ ‖ζ‖
    rw [hζ]
  have hcont : ∀ j, ContinuousOn (fun ζ => g ζ / (∏ k, (ζ - z k)) * b j ζ)
      (Metric.sphere (0 : ℂ) r) := by
    intro j
    refine ContinuousOn.mul ?_ (hbc j).continuousOn
    exact (hg.continuousOn.mono hsph).div (by fun_prop) hPne
  obtain ⟨c, hc⟩ : ∃ c : Fin l → ℂ,
      c = fun j => -(2 * (Real.pi : ℂ) * I)⁻¹ * ∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ :=
    ⟨_, rfl⟩
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨c, fun i => ?_, ?_⟩
  · have hwi := (hz i).1
    have e1 : ∑ j, c j * z i ^ (j : ℕ) = -(2 * (Real.pi : ℂ) * I)⁻¹ *
        ∑ j : Fin l, ∮ ζ in C(0, r), z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [circleIntegral.integral_smul, hc, smul_eq_mul]
      ring
    rw [e1, ← circleIntegral_finset_sum' Finset.univ
      (fun (j : Fin l) ζ => z i ^ (j : ℕ) • ((g ζ / ∏ k, (ζ - z k)) * b j ζ)) 0 r
      (fun j _ => ContinuousOn.circleIntegrable hr.le ((hcont j).const_smul (z i ^ (j : ℕ))))]
    have e2 : (∮ ζ in C(0, r), ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ))
        = ∮ ζ in C(0, r), (ζ - z i)⁻¹ * g ζ := by
      apply circleIntegral.integral_congr hr.le
      intro ζ hζ
      have hPζ := hPne ζ hζ
      have hzne : ζ - z i ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [mem_sphere_zero_iff_norm, h] at hζ
        rw [hζ] at hwi
        exact lt_irrefl _ hwi
      have e := hbid ζ (z i)
      have hPz : ∏ k, (z i - z k) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      rw [hPz, sub_zero] at e
      have hsum : ∑ j, b j ζ * z i ^ (j : ℕ) = (∏ k, (ζ - z k)) / (ζ - z i) :=
        eq_div_of_mul_eq hzne e
      have e3 : ∑ j : Fin l, z i ^ (j : ℕ) • (g ζ / (∏ k, (ζ - z k)) * b j ζ)
          = g ζ / (∏ k, (ζ - z k)) * ∑ j, b j ζ * z i ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_eq_mul]
        ring
      simp only
      rw [e3, hsum]
      field_simp
    rw [e2, cauchy_exterior g r hr hg h0 (z i) hwi]
    field_simp
  · have hsph1 : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖ζ‖ = r := fun ζ hζ =>
      mem_sphere_zero_iff_norm.mp hζ
    have hG0 : 0 ≤ G := by
      have hmem : ((r : ℂ)) ∈ Metric.sphere (0 : ℂ) r := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hpos : 0 < ‖∏ k, ((r : ℂ) - z k)‖ := norm_pos_iff.mpr (hPne _ hmem)
      have h1 := hG (r : ℂ) (hsph1 _ hmem)
      by_contra hneg
      have hlt : G * ‖∏ k, ((r : ℂ) - z k)‖ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
      linarith [norm_nonneg (g (r : ℂ))]
    have hbound : ∀ j, ∀ ζ ∈ Metric.sphere (0 : ℂ) r,
        ‖g ζ / (∏ k, (ζ - z k)) * b j ζ‖ ≤ G * 2 ^ l := by
      intro j ζ hζ
      have hpos : 0 < ‖∏ k, (ζ - z k)‖ := norm_pos_iff.mpr (hPne ζ hζ)
      have hq : ‖g ζ‖ / ‖∏ k, (ζ - z k)‖ ≤ G := by
        rw [div_le_iff₀ hpos]
        exact hG ζ (hsph1 ζ hζ)
      have hb := hbb j ζ (by rw [hsph1 ζ hζ]; exact hr1)
      rw [norm_mul, norm_div]
      exact mul_le_mul hq hb (norm_nonneg _) hG0
    have hcj : ∀ j, ‖c j‖ ≤ 2 ^ l * (r * G) := by
      intro j
      have hI := circleIntegral.norm_integral_le_of_norm_le_const hr.le (hbound j)
      have hn : ‖-(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
        rw [norm_neg, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
        norm_num
      rw [hc]
      simp only
      rw [norm_mul, hn]
      calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, r), g ζ / (∏ k, (ζ - z k)) * b j ζ‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r * (G * 2 ^ l)) := by
            gcongr
        _ = 2 ^ l * (r * G) := by
            field_simp
    have hl : (l : ℝ) ≤ 2 ^ l := by exact_mod_cast (Nat.lt_two_pow_self (n := l)).le
    calc ∑ j, ‖c j‖ ≤ ∑ _j : Fin l, 2 ^ l * (r * G) := Finset.sum_le_sum (fun j _ => hcj j)
      _ = (l : ℝ) * (2 ^ l * (r * G)) := by simp
      _ ≤ 2 ^ l * (2 ^ l * (r * G)) := by
          gcongr
      _ = 4 ^ l * r * G := by
          rw [show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]
          ring

end GlobalTheory.ExteriorInterpolation
