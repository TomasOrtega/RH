import Mathlib
open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.PosDefFT

/- English proof (translation)
Use `set I := ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) with hI`. Establish `key : ∀ k : ℕ, 0 ≤ (k : ℂ) * (ψ 0 - I + k * I)`. Introduce `k`. Set `P : Measure (Fin k → ℝ)` to `Measure.pi (fun _ => μ)`. Establish `hint : ∀ i j : Fin k, Integrable (fun t : Fin k → ℝ => ψ (t j - t i)) P`.

Introduce `i j`. Use `Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)` and prove the remaining obligations. Conclude with `(hc.comp (by fun_prop)).aestronglyMeasurable`. Establish `hval : ∀ i j : Fin k, ∫ t, ψ (t j - t i) ∂P = (if i = j then ψ 0 - I else 0) + I`. Introduce `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `hind : ProbabilityTheory.iIndepFun (fun (i : Fin k) (t : Fin k → ℝ) => t i) P` using `ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)`. Establish `h2` using `hind.indepFun h`.

Rewrite `h2` using `[ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]`. Establish `e : ∀ l : Fin k, P.map (fun t => t l) = μ` using `fun l => (measurePreserving_eval (fun _ : Fin k => μ) l).map_eq`. Rewrite `h2` using `[e, e]`. Rewrite using `[if_neg h, zero_add, hI, ← h2, integral_map (by fun_prop)]`. Conclude with `(hc.comp (by fun_prop)).aestronglyMeasurable`.

Establish `h0 : 0 ≤ ∫ t, ∑ i, ∑ j, ψ (t j - t i) ∂P` using `integral_nonneg (fun t => hp k t)`. Rewrite `h0` using `[integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]`. Rewrite `h0` using `[integral_finset_sum _ (fun j _ => hint _ j), hval]`. Simplify `h0` using `[Finset.sum_add_distrib, mul_add]`. Establish `key2 : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I`.

Introduce `k`. Establish `h1` using `key (k + 1)`. Establish `h2 : (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) ^ 2` using `by positivity`. Establish `h3` using `smul_nonneg h2 h1`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Establish `: ((k : ℂ) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I) atTop (𝓝 ((0 : ℝ) • (ψ 0 - I) + I))` using `(tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _).add_const _`.

Simplify using `using ge_of_tendsto' hlim key2`.
-/
theorem integral_prod_nonneg (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) := by
  set I := ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) with hI
  have key : ∀ k : ℕ, 0 ≤ (k : ℂ) * (ψ 0 - I + k * I) := by
    intro k
    let P : Measure (Fin k → ℝ) := Measure.pi (fun _ => μ)
    have hint : ∀ i j : Fin k, Integrable (fun t : Fin k → ℝ => ψ (t j - t i)) P := by
      intro i j
      refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
      exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have hval : ∀ i j : Fin k, ∫ t, ψ (t j - t i) ∂P = (if i = j then ψ 0 - I else 0) + I := by
      intro i j
      by_cases h : i = j
      · subst h
        simp
      · have hind : ProbabilityTheory.iIndepFun (fun (i : Fin k) (t : Fin k → ℝ) => t i) P :=
          ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
        have h2 := hind.indepFun h
        rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable] at h2
        have e : ∀ l : Fin k, P.map (fun t => t l) = μ := fun l =>
          (measurePreserving_eval (fun _ : Fin k => μ) l).map_eq
        rw [e, e] at h2
        rw [if_neg h, zero_add, hI, ← h2, integral_map (by fun_prop)]
        exact (hc.comp (by fun_prop)).aestronglyMeasurable
    have h0 : 0 ≤ ∫ t, ∑ i, ∑ j, ψ (t j - t i) ∂P := integral_nonneg (fun t => hp k t)
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))] at h0
    simp_rw [integral_finset_sum _ (fun j _ => hint _ j), hval] at h0
    simpa [Finset.sum_add_distrib, mul_add] using h0
  have key2 : ∀ k : ℕ, 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I := by
    intro k
    have h1 := key (k + 1)
    have h2 : (0 : ℝ) ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by positivity
    have h3 := smul_nonneg h2 h1
    convert h3 using 1
    have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ) • (ψ 0 - I) + I) atTop
      (𝓝 ((0 : ℝ) • (ψ 0 - I) + I)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _).add_const _
  simpa using ge_of_tendsto' hlim key2

/- English proof (translation)
Set `μ : Measure ℝ` to `volume.restrict (Set.Ioo 0 1)`. Use `haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩`. Set `G : ℕ → ℝ → ℂ` to `fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s`. Establish `hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ`. Introduce `n x`.

Establish `h` using `intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ) ((n : ℝ) * x)`. Rewrite `h` using `[intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]`. Simplify using `only [G, μ, mul_sub]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Establish `hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ)`. Introduce `n`. Use `Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)` and prove the remaining obligations. Conclude with `(hc.comp (by fun_prop)).aestronglyMeasurable`. Establish `hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ`.

Introduce `n`. Establish `h` using `integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ`. Rewrite `h` using `[integral_prod _ (hint n)]`. Repeatedly rewrite using `[hG, integral_smul]`. Conclude with `smul_nonneg (Nat.cast_nonneg n) h`.

Establish `hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ))`. Use `tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_ (integrable_const _) ?_ ?_` and prove the remaining obligations. Introduce `n`. Establish `: G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ` using `funext (hG n)`. Rewrite using `[this]`.

Conclude with `((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable`. Introduce `n`. Use `Eventually.of_forall fun x => ?_` and prove the remaining obligations. Use `(intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_` and prove the remaining obligations. Conclude with `setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)`.

Use `(ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Use `intervalIntegral_tendsto_integral hi ?_ ?_` and prove the remaining obligations. Conclude with `tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)`. Conclude with `tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)`. Simplify using `using ge_of_tendsto' hlim hnn`.
-/
theorem integral_nonneg_of_sums (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let G : ℕ → ℝ → ℂ := fun n x => ∫ s in (-((n : ℝ) * x))..((n : ℝ) * (1 - x)), ψ s
  have hG : ∀ n x, G n x = (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := by
    intro n x
    have h := intervalIntegral.smul_integral_comp_mul_sub (f := ψ) (a := 0) (b := 1) (n : ℝ)
      ((n : ℝ) * x)
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
    simp only [G, μ, mul_sub]
    rw [h]
    simp
  have hint : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ψ ((n : ℝ) * (p.2 - p.1))) (μ.prod μ) := by
    intro n
    refine Integrable.of_bound ?_ C (Eventually.of_forall fun t => hb _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  have hnn : ∀ n, 0 ≤ ∫ x, G n x ∂μ := by
    intro n
    have h := integral_prod_nonneg (fun s => ψ ((n : ℝ) * s)) (hc.comp (by fun_prop)) C
      (fun s => hb _) (fun k t => by simpa [mul_sub] using hp k (fun i => (n : ℝ) * t i)) μ
    rw [integral_prod _ (hint n)] at h
    simp_rw [hG, integral_smul]
    exact smul_nonneg (Nat.cast_nonneg n) h
  have hlim : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ _x, (∫ s, ψ s) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ s, ‖ψ s‖) ?_
      (integrable_const _) ?_ ?_
    · intro n
      have : G n = fun x => (n : ℝ) • ∫ y, ψ ((n : ℝ) * (y - x)) ∂μ := funext (hG n)
      rw [this]
      exact ((hint n).integral_prod_left.smul (n : ℝ)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_le_integral hi.norm (Eventually.of_forall fun _ => norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      refine intervalIntegral_tendsto_integral hi ?_ ?_
      · exact tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hx.1)
      · exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hx.2)
  simpa using ge_of_tendsto' hlim hnn

/- English proof (translation)
Introduce and unpack `φ hc ⟨A, e, he, hb⟩ hp ξ`. Establish `hn : ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ξ * s)) * φ s‖ = ‖φ s‖`. Introduce `s`. Rewrite using `[norm_mul, Complex.norm_exp]`. Simplify using the standard rewrite rules.

Establish `hc' : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s` using `by fun_prop`. Establish `hA : 0 ≤ A` using `by simpa using (norm_nonneg _).trans (hb 0)`. Use `integral_nonneg_of_sums _ hc' A (fun s => ?_) ?_ (fun k t => ?_)` and prove the remaining obligations. Rewrite using `[hn]`. Use `(hb s).trans (mul_le_of_le_one_right hA ?_)` and prove the remaining obligations.

Rewrite using `[Real.exp_le_one_iff, neg_nonpos]`. Check the signs of the components of the expression. Establish `h1 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Ioi 0)`. Use `(exp_neg_integrableOn_Ioi 0 he).congr_fun (fun s hs => ?_) measurableSet_Ioi` and prove the remaining obligations. Simplify using `[abs_of_pos (Set.mem_Ioi.1 hs)]`.

Establish `h2 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Iic 0)`. Use `(integrableOn_exp_mul_Iic he 0).congr_fun (fun s hs => ?_) measurableSet_Iic` and prove the remaining obligations. Simplify using `[abs_of_nonpos (Set.mem_Iic.1 hs)]`. Establish `h3 : Integrable (fun s : ℝ => Real.exp (-(e * |s|)))`. Use `h2.union h1` as an intermediate fact.

Rewrite `this` using `[Set.Iic_union_Ioi, integrableOn_univ]`. Then use the resulting hypothesis. Use `(h3.const_mul A).mono' hc'.aestronglyMeasurable (Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Rewrite using `[hn]`. Conclude with `hb s`. Use `hp k t (fun j => Complex.exp (-(Complex.I * ξ * t j))) using 4 with i _ j _` and compare the differences between its conclusion and the goal.

Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_nonneg : ∀ φ : ℝ → ℂ, Continuous φ →
    (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
    (∀ (k : ℕ) (t : Fin k → ℝ) (z : Fin k → ℂ),
      0 ≤ ∑ i, ∑ j, star (z i) * z j * φ (t j - t i)) →
    ∀ ξ : ℝ, 0 ≤ ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s := by
  rintro φ hc ⟨A, e, he, hb⟩ hp ξ
  have hn : ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ξ * s)) * φ s‖ = ‖φ s‖ := by
    intro s
    rw [norm_mul, Complex.norm_exp]
    simp
  have hc' : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ξ * s)) * φ s := by fun_prop
  have hA : 0 ≤ A := by simpa using (norm_nonneg _).trans (hb 0)
  refine integral_nonneg_of_sums _ hc' A (fun s => ?_) ?_ (fun k t => ?_)
  · rw [hn]
    refine (hb s).trans (mul_le_of_le_one_right hA ?_)
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  · have h1 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 he).congr_fun (fun s hs => ?_) measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.1 hs)]
    have h2 : IntegrableOn (fun s : ℝ => Real.exp (-(e * |s|))) (Set.Iic 0) := by
      refine (integrableOn_exp_mul_Iic he 0).congr_fun (fun s hs => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.1 hs)]
    have h3 : Integrable (fun s : ℝ => Real.exp (-(e * |s|))) := by
      have := h2.union h1
      rwa [Set.Iic_union_Ioi, integrableOn_univ] at this
    refine (h3.const_mul A).mono' hc'.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [hn]
    exact hb s
  · convert hp k t (fun j => Complex.exp (-(Complex.I * ξ * t j))) using 4 with i _ j _
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp
    ring

end GlobalTheory.PosDefFT
