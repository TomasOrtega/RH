import Mathlib

noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace PositivityTheory.SiegelWeilFormula.Holtb

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/- English proof (translation)
Set `b` to `Module.finBasis ℂ E`. Set `L : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ` to `fun i => LinearMap.toContinuousLinearMap (b.coord i)`. Establish `hrep : ∀ x, fderiv ℂ (f x) W₀ = ∑ i, fderiv ℂ (f x) W₀ (b i) • L i`. Introduce `x`. Use extensionality with `v`.

Simplify using `only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, L, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]`. Use `conv_lhs => rw [← b.sum_repr v]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.

Establish `hfun : (fun x => fderiv ℂ (f x) W₀) = fun x => ∑ i, fderiv ℂ (f x) W₀ (b i) • L i` using `funext hrep`. Rewrite using `[hfun]`. Use `Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_` and prove the remaining obligations. Use `AEStronglyMeasurable.smul_const ?_ (L i)` and prove the remaining obligations. Use `set v := b i`.

Use `set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def`. Establish `hε : 0 < ε` using `by positivity`. Use `set t : ℕ → ℂ := fun k => ((ε * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with ht_def`. Establish `ht0 : Tendsto t atTop (𝓝[≠] 0)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩` and prove the remaining obligations.

Establish `h` using `(tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)`. Rewrite `h` using `[mul_zero]`. Establish `h2` using `(Complex.continuous_ofReal.tendsto 0).comp h`. Simplify `h2` using `[ht_def, Function.comp_def]`. Simplify using `only [ht_def, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]`.

Check the signs of the components of the expression. Establish `htn : ∀ k, ‖t k‖ ≤ ε`. Introduce `k`. Simplify using `only [ht_def, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[abs_of_nonneg (by positivity)]`.

Establish `: 1 / ((k : ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `htmem : ∀ k, W₀ + t k • v ∈ ball W₀ r`. Introduce `k`.

Rewrite using `[mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Establish `h1 : ε * (‖v‖ + 1) = r / 2` using `by rw [hε_def]; field_simp`. Establish `h2 : ‖t k‖ * ‖v‖ ≤ ε * (‖v‖ + 1)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.

Use `aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun k x => (t k)⁻¹ • (f x (W₀ + t k • v) - f x W₀)) (fun k => ?_) (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Conclude with `(((hm _ (htmem k)).sub (hm _ (mem_ball_self hr))).const_smul ((t k)⁻¹)).congr (ae_of_all _ fun x => rfl)`. Establish `hl : HasDerivAt (fun s : ℂ => W₀ + s • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add W₀`. Establish `h1 : HasDerivAt (fun s : ℂ => f x (W₀ + s • v)) (fderiv ℂ (f x) W₀ v) 0` using `(hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)`.

Establish `h2` using `h1.tendsto_slope_zero.comp ht0`. Simplify `h2` using `[Function.comp_def]`.
-/
theorem aesm_fderiv (f : X → E → ℂ) (W₀ : E) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x, DifferentiableAt ℂ (f x) W₀)
    (hm : ∀ W ∈ ball W₀ r, AEStronglyMeasurable (f · W) ν) :
    AEStronglyMeasurable (fun x => fderiv ℂ (f x) W₀) ν := by
  classical
  let b := Module.finBasis ℂ E
  let L : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hrep : ∀ x, fderiv ℂ (f x) W₀ = ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := by
    intro x
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, L, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hfun : (fun x => fderiv ℂ (f x) W₀) = fun x => ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := funext hrep
  rw [hfun]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ (L i)
  set v := b i
  set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  set t : ℕ → ℂ := fun k => ((ε * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with ht_def
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)
      rw [mul_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [ht_def, Function.comp_def] using h2
    · simp only [ht_def, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have htn : ∀ k, ‖t k‖ ≤ ε := by
    intro k
    simp only [ht_def, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have htmem : ∀ k, W₀ + t k • v ∈ ball W₀ r := by
    intro k
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ε * (‖v‖ + 1) = r / 2 := by rw [hε_def]; field_simp
    have h2 : ‖t k‖ * ‖v‖ ≤ ε * (‖v‖ + 1) := by
      calc ‖t k‖ * ‖v‖ ≤ ε * ‖v‖ := by gcongr; exact htn k
        _ ≤ ε * (‖v‖ + 1) := by nlinarith
    linarith
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun k x => (t k)⁻¹ • (f x (W₀ + t k • v) - f x W₀)) (fun k => ?_) (ae_of_all _ fun x => ?_)
  · exact (((hm _ (htmem k)).sub (hm _ (mem_ball_self hr))).const_smul ((t k)⁻¹)).congr (ae_of_all _ fun x => rfl)
  · have hl : HasDerivAt (fun s : ℂ => W₀ + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add W₀
    have h1 : HasDerivAt (fun s : ℂ => f x (W₀ + s • v)) (fderiv ℂ (f x) W₀ v) 0 :=
      (hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    have h2 := h1.tendsto_slope_zero.comp ht0
    simpa [Function.comp_def] using h2

/- English proof (translation)
Introduce `W₀ hW₀`. Take `⟨r, hr, M, hsub, hM⟩` from `hb W₀ hW₀`. Use `set M' := max M 0`. Establish `hM' : ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M'` using `fun x W hW => (hM x W hW).trans (le_max_left _ _)`. Establish `hdiffAt : ∀ x, ∀ W ∈ ball W₀ r, DifferentiableAt ℂ (f x) W` using `fun x W hW => (hd x).differentiableAt (hU.mem_nhds (hsub hW))`.

Establish `hball : ∀ W ∈ ball W₀ (r / 2), ball W (r / 2) ⊆ ball W₀ r`. Introduce `W hW`. Apply `ball_subset_ball'` to reduce the goal to its premises. Rewrite `hW` using `[mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbnd : ∀ x, ∀ W ∈ ball W₀ (r / 2), ‖fderiv ℂ (f x) W‖ ≤ (2 * M') / (r / 2)`. Introduce `x W hW`. Apply `Complex.norm_fderiv_le_div_of_mapsTo_ball` to reduce the goal to its premises. Conclude with `(hd x).mono ((hball W hW).trans hsub)`. Introduce `Z hZ`.

Rewrite using `[mem_closedBall, dist_eq_norm]`. Establish `hZ' : Z ∈ ball W₀ r` using `hball W hW hZ`. Establish `hW' : W ∈ ball W₀ r` using `ball_subset_ball (by linarith) hW`. Combine the equalities or inequalities in the displayed calculation. Check the signs of the components of the expression.

Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun W x => f x W) (F' := fun W x => fderiv ℂ (f x) W) (bound := fun _ => (2 * M') / (r / 2)) (s := ball W₀ (r / 2)) (x₀ := W₀) (ball_mem_nhds W₀ (by positivity)) (eventually_of_mem (hU.mem_nhds hW₀) fun W hW => hm W hW …`. Conclude with `key.differentiableAt.differentiableWithinAt`.
-/
theorem differentiableOn_integral_of_bdd [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (f : X → E → ℂ)
    (hd : ∀ x, DifferentiableOn ℂ (f x) U) (hm : ∀ W ∈ U, AEStronglyMeasurable (f · W) ν)
    (hb : ∀ W₀ ∈ U, ∃ r > 0, ∃ M, ball W₀ r ⊆ U ∧ ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M) :
    DifferentiableOn ℂ (fun W => ∫ x, f x W ∂ν) U := by
  intro W₀ hW₀
  obtain ⟨r, hr, M, hsub, hM⟩ := hb W₀ hW₀
  set M' := max M 0
  have hM' : ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M' := fun x W hW => (hM x W hW).trans (le_max_left _ _)
  have hdiffAt : ∀ x, ∀ W ∈ ball W₀ r, DifferentiableAt ℂ (f x) W := fun x W hW =>
    (hd x).differentiableAt (hU.mem_nhds (hsub hW))
  have hball : ∀ W ∈ ball W₀ (r / 2), ball W (r / 2) ⊆ ball W₀ r := by
    intro W hW
    apply ball_subset_ball'
    rw [mem_ball] at hW
    linarith
  have hbnd : ∀ x, ∀ W ∈ ball W₀ (r / 2), ‖fderiv ℂ (f x) W‖ ≤ (2 * M') / (r / 2) := by
    intro x W hW
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
    · exact (hd x).mono ((hball W hW).trans hsub)
    · intro Z hZ
      rw [mem_closedBall, dist_eq_norm]
      have hZ' : Z ∈ ball W₀ r := hball W hW hZ
      have hW' : W ∈ ball W₀ r := ball_subset_ball (by linarith) hW
      calc ‖f x Z - f x W‖ ≤ ‖f x Z‖ + ‖f x W‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add (hM' x Z hZ') (hM' x W hW')
        _ = 2 * M' := by ring
    · positivity
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun W x => f x W)
    (F' := fun W x => fderiv ℂ (f x) W) (bound := fun _ => (2 * M') / (r / 2)) (s := ball W₀ (r / 2)) (x₀ := W₀)
    (ball_mem_nhds W₀ (by positivity))
    (eventually_of_mem (hU.mem_nhds hW₀) fun W hW => hm W hW)
    ((integrable_const M').mono' (hm W₀ hW₀) (ae_of_all _ fun x => hM' x W₀ (mem_ball_self hr)))
    (aesm_fderiv f W₀ r hr (fun x => hdiffAt x W₀ (mem_ball_self hr)) (fun W hW => hm W (hsub hW)))
    (ae_of_all _ fun x W hW => hbnd x W hW)
    (integrable_const _)
    (ae_of_all _ fun x W hW => (hdiffAt x W (ball_subset_ball (by linarith) hW)).hasFDerivAt)
  exact key.differentiableAt.differentiableWithinAt

end PositivityTheory.SiegelWeilFormula.Holtb
