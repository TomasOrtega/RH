import Mathlib
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.AvgSmooth

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}

/- English proof (translation)
Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hf.continuousOn`. Conclude with `Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))`.
-/
theorem integrable_cont (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def coordC (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (1 : ℂ)

/- English proof (translation)
Use `ext1 u`. Establish `e : L u = ∑ i, u i • L (Pi.single i 1)` using `by conv_lhs => rw [← Finset.univ_sum_single u]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul]`.

Use `congr 1`. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Rewrite using `[e]`. Simplify using `[coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]`.
-/
theorem clm_expand (L : (Fin n → ℝ) →L[ℝ] ℂ) : L = ∑ i, L (Pi.single i 1) • coordC n i := by
  ext1 u
  have e : L u = ∑ i, u i • L (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

/- English proof (translation)
Establish `hFk : ∀ t, Continuous fun k => F k t` using `fun t => hF.comp (continuous_id.prodMk continuous_const)`. Establish `hGk : ∀ i t, Continuous fun k => G i k t` using `fun i t => (hG i).comp (continuous_id.prodMk continuous_const)`. Establish `hM : ∀ i, ∃ M : ℝ, ∀ p ∈ (Set.univ : Set K) ×ˢ Metric.closedBall t₀ 1, ‖G i p.1 p.2‖ ≤ M` using `fun i => (isCompact_univ.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn (hG i).continuousOn`. Use `choose M hM using hM`. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F := fun t k => F k t) (F' := fun t k => ∑ i, G i k t • coordC n i) (bound := fun _ => ∑ i, M i * ‖coordC n i‖) (Metric.ball_mem_nhds t₀ one_pos) (Filter.Eventually.of_forall fun t => (hFk t).aestronglyMeasurable) (integrab …`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`. Use `gcongr`. Conclude with `hM i (k, t) ⟨Set.mem_univ _, Metric.ball_subset_closedBall ht⟩)`. Use the proof step `(integrable_const _)`.

Use the proof step `(Filter.Eventually.of_forall fun k t _ => by`. Establish `h` using `(hd k t).hasFDerivAt`. Rewrite `h` using `[clm_expand (fderiv ℝ (F k) t)]`. Simplify `h)` using `only [he]`. Use `key.congr_fderiv ?_` and prove the remaining obligations.

Rewrite using `[integral_finset_sum _ fun i _ => (integrable_cont μ (hGk i t₀)).smul_const _]`. Conclude with `Finset.sum_congr rfl fun i _ => integral_smul_const _ _`.
-/
theorem hasFDerivAt_avg (μ : Measure K) [IsFiniteMeasure μ] {F : K → (Fin n → ℝ) → ℂ}
    {G : Fin n → K → (Fin n → ℝ) → ℂ} (hF : Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2)
    (hG : ∀ i, Continuous fun p : K × (Fin n → ℝ) => G i p.1 p.2) (hd : ∀ k, Differentiable ℝ (F k))
    (he : ∀ i k t, fderiv ℝ (F k) t (Pi.single i 1) = G i k t) (t₀ : Fin n → ℝ) :
    HasFDerivAt (fun t => ∫ k, F k t ∂μ) (∑ i, (∫ k, G i k t₀ ∂μ) • coordC n i) t₀ := by
  have hFk : ∀ t, Continuous fun k => F k t := fun t => hF.comp (continuous_id.prodMk continuous_const)
  have hGk : ∀ i t, Continuous fun k => G i k t := fun i t => (hG i).comp (continuous_id.prodMk continuous_const)
  have hM : ∀ i, ∃ M : ℝ, ∀ p ∈ (Set.univ : Set K) ×ˢ Metric.closedBall t₀ 1, ‖G i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_univ.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn (hG i).continuousOn
  choose M hM using hM
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun t k => F k t) (F' := fun t k => ∑ i, G i k t • coordC n i)
    (bound := fun _ => ∑ i, M i * ‖coordC n i‖) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hFk t).aestronglyMeasurable)
    (integrable_cont μ (hFk t₀))
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGk i t₀).aestronglyMeasurable.smul_const _)
    (Filter.Eventually.of_forall fun k t ht => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      gcongr
      exact hM i (k, t) ⟨Set.mem_univ _, Metric.ball_subset_closedBall ht⟩)
    (integrable_const _)
    (Filter.Eventually.of_forall fun k t _ => by
      have h := (hd k t).hasFDerivAt
      rw [clm_expand (fderiv ℝ (F k) t)] at h
      simpa only [he] using h)
  refine key.congr_fderiv ?_
  rw [integral_finset_sum _ fun i _ => (integrable_cont μ (hGk i t₀)).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

end GlobalTheory.AvgSmooth

open GlobalTheory.AvgSmooth in

/- English proof (translation)
Introduce `K _ _ _ _ μ _ n φ hφ 𝒢 hc hd hder`. Establish `hk : ∀ F ∈ 𝒢, ∀ t, Integrable (fun k => F k t) μ` using `fun F hF t => integrable_cont μ ((hc F hF).comp (continuous_id.prodMk continuous_const))`. Establish `hD : ∀ F ∈ 𝒢, ∃ F' : Fin n → K → (Fin n → ℝ) → ℂ, (∀ i, F' i ∈ 𝒢) ∧ ∀ t₀, HasFDerivAt (fun t => ∫ k, F k t ∂μ) (∑ i, ((∫ k, F' i k t₀ ∂μ) + φ i t₀ * ∫ k, F k t₀ ∂μ) • coordC n i) t₀`. Introduce `F hF`. Use `choose F' hF' he using hder F hF`.

Use `⟨F', hF', fun t₀ => ?_⟩` and prove the remaining obligations. Establish `h` using `hasFDerivAt_avg μ (G := fun i k t => F' i k t + φ i t * F k t) (hc F hF) (fun i => (hc _ (hF' i)).add (((hφ i).continuous.comp continuous_snd).mul (hc F hF))) (hd F hF) he t₀`. Use `h.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_add (hk _ (hF' i) t₀) ((hk F hF t₀).const_mul _), integral_const_mul]`. Establish `main : ∀ m : ℕ, ∀ F ∈ 𝒢, ContDiff ℝ m fun t => ∫ k, F k t ∂μ`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `F hF`. Take `⟨F', -, h⟩` from `hD F hF`.

Conclude with `contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)`. Consider the case `succ m ih`. Introduce `F hF`. Take `⟨F', hF', h⟩` from `hD F hF`. Rewrite using `[show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]`.

Use `⟨_, ?_, h⟩` and prove the remaining obligations. Use `ContDiff.sum fun i _ => ContDiff.smul_const ?_ _` and prove the remaining obligations. Conclude with `(ih _ (hF' i)).add ((contDiff_infty.1 (hφ i) m).mul (ih F hF))`. Introduce `F hF`. Conclude with `contDiff_infty.2 fun m => main m F hF`.
-/
theorem GlobalTheory.AvgSmooth.main : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  intro K _ _ _ _ μ _ n φ hφ 𝒢 hc hd hder
  have hk : ∀ F ∈ 𝒢, ∀ t, Integrable (fun k => F k t) μ := fun F hF t =>
    integrable_cont μ ((hc F hF).comp (continuous_id.prodMk continuous_const))
  have hD : ∀ F ∈ 𝒢, ∃ F' : Fin n → K → (Fin n → ℝ) → ℂ, (∀ i, F' i ∈ 𝒢) ∧ ∀ t₀,
      HasFDerivAt (fun t => ∫ k, F k t ∂μ)
        (∑ i, ((∫ k, F' i k t₀ ∂μ) + φ i t₀ * ∫ k, F k t₀ ∂μ) • coordC n i) t₀ := by
    intro F hF
    choose F' hF' he using hder F hF
    refine ⟨F', hF', fun t₀ => ?_⟩
    have h := hasFDerivAt_avg μ (G := fun i k t => F' i k t + φ i t * F k t) (hc F hF)
      (fun i => (hc _ (hF' i)).add (((hφ i).continuous.comp continuous_snd).mul (hc F hF))) (hd F hF) he t₀
    refine h.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)
    rw [integral_add (hk _ (hF' i) t₀) ((hk F hF t₀).const_mul _), integral_const_mul]
  have main : ∀ m : ℕ, ∀ F ∈ 𝒢, ContDiff ℝ m fun t => ∫ k, F k t ∂μ := by
    intro m
    induction m with
    | zero =>
      intro F hF
      obtain ⟨F', -, h⟩ := hD F hF
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)
    | succ m ih =>
      intro F hF
      obtain ⟨F', hF', h⟩ := hD F hF
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, h⟩
      refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
      exact (ih _ (hF' i)).add ((contDiff_infty.1 (hφ i) m).mul (ih F hF))
  intro F hF
  exact contDiff_infty.2 fun m => main m F hF

end
