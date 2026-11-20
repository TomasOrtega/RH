import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionCompositionStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Helpers

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use function extensionality and compare the values at `q`. Simplify using `only [affCoord]`. Conclude with `mul_div_mul_left _ _ (hc q.1)`.
-/
theorem affCoord_eq_of_orbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `[affCoord, cj, map_div₀]`.
-/
theorem affCoord_cj (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) :
    affCoord p (cj z) = cj (affCoord p z) := by
  funext q
  simp [affCoord, cj, map_div₀]

/- English proof (translation)
Take `⟨c, -, rfl⟩` from `h`. Introduce `h0`. Conclude with `hq (by simp [cj, h0])`.
-/
theorem ne_zero_of_orbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z (cj z')) {q : Σ k, ι k}
    (hq : z q ≠ 0) : z' q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h0
  exact hq (by simp [cj, h0])

/- English proof (translation)
Rewrite using `[analyticAt_pi_iff]`. Introduce `q`. Conclude with `(hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)`.
-/
theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Σ k, ι k) → ℂ} {a : E} (p : (k : K) → ι k)
    (hf : ∀ q, AnalyticAt ℂ (fun y => f y q) a) (h0 : ∀ k, f a ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun y => affCoord p (f y)) a := by
  rw [analyticAt_pi_iff]
  intro q
  exact (hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)

/- English proof (translation)
Use `GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_` and prove the remaining obligations. Establish `hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w)`. Simplify using `using (continuous_star.tendsto (star w))`. Use `filter_upwards [hs.eventually h.eventually_analyticAt] with v hv`. Simplify using `using hv.differentiableAt.star_star`.
-/
theorem analyticAt_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : AnalyticAt ℂ ψ w) : AnalyticAt ℂ (star ∘ ψ ∘ star) (star w) := by
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  have hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w) := by
    simpa using (continuous_star.tendsto (star w))
  filter_upwards [hs.eventually h.eventually_analyticAt] with v hv
  simpa using hv.differentiableAt.star_star

/- English proof (translation)
Rewrite using `[h.hasFDerivAt.star_star.fderiv, eq_bot_iff]`. Introduce `v hv`. Establish `hv' : star (fderiv ℂ ψ w (star v)) = 0` using `by simpa using hv`. Establish `h1 : fderiv ℂ ψ w (star v) = 0` using `by simpa using hv'`. Establish `h2 : star v ∈ (fderiv ℂ ψ w).ker` using `by simpa using h1`.

Rewrite `h2` using `[hk]`. Establish `h3 : star v = 0` using `by simpa using h2`. Simplify using `using h3`.
-/
theorem ker_fderiv_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : DifferentiableAt ℂ ψ w) (hk : (fderiv ℂ ψ w).ker = ⊥) :
    (fderiv ℂ (star ∘ ψ ∘ star) (star w)).ker = ⊥ := by
  rw [h.hasFDerivAt.star_star.fderiv, eq_bot_iff]
  intro v hv
  have hv' : star (fderiv ℂ ψ w (star v)) = 0 := by simpa using hv
  have h1 : fderiv ℂ ψ w (star v) = 0 := by simpa using hv'
  have h2 : star v ∈ (fderiv ℂ ψ w).ker := by simpa using h1
  rw [hk] at h2
  have h3 : star v = 0 := by simpa using h2
  simpa using h3

end Helpers

/- English proof (translation)
Introduce `K _ ι _ e X _ A P U lift hL c hc hcc j k w hw`. Take `⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩` from `hL`. Take `⟨hw1, hw2⟩` from `hw`. Establish `hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source` using `hw2`. Generalize the expression as in `hx₀ : (A.chart j).symm w = x₀ at hw2'`.

Generalize the expression as in `hx₁ : c x₀ = x₁ at hw2'`. Use `choose p hp using (hM x₁ x₁ (hUm x₁)).1`. Establish `hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0` using `fun b => ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)`. Establish `hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁` using `(A.chart k).left_inv hw2'`. Establish `hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁)`.

Use `analyticAt_affCoord p (fun q => ?_) (fun b => ?_)` and prove the remaining obligations. Conclude with `hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩`. Simplify `hp b` using `[hsym₁]`. Establish `hker` using `hIm x₁ p hp k hw2'`. Establish `hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w`.

Use `analyticAt_affCoord p (fun q => ?_) (fun b => ?_)` and prove the remaining obligations. Conclude with `hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩`. Simplify `hp0 b` using `[hx₀]`. Establish `hsc : ContinuousAt (A.chart j).symm w` using `(A.chart j).continuousAt_symm hw1`. Establish `hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w` using `hcc.continuousAt.comp hsc`.

Establish `hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w`. Establish `h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w))`. Rewrite using `[hx₀, hx₁]`. Conclude with `(A.chart k).continuousAt hw2'`. Conclude with `continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)`.

Establish `hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁)`. Rewrite using `[hx₀, hx₁]`. Establish `e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀` using `hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))`. Establish `e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁` using `hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by`. Express the relevant statement in the definitionally equal form `c ((A.chart j).symm w) ∈ _`.

Rewrite using `[hx₀, hx₁]`. Conclude with `⟨hw2', hUm x₁⟩))`. Use `GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z)))) (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star) (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_` and prove the remaining obligations. Rewrite using `[hFw]`. Conclude with `analyticAt_star_comp hψ`.

Rewrite using `[hFw]`. Conclude with `ker_fderiv_star_comp hψ.differentiableAt hker`. Use `filter_upwards [e1, e2] with y h1 h2`. Take `⟨h2s, h2u⟩` from `h2`. Generalize the expression as in `hy' : (A.chart j).symm y = y' at h1 h2s h2u`.

Establish `ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y'))` using `hCp _ _ _ ⟨h2u, hUm _⟩`. Establish `ho2 : SameOrbit (lift y' y') (lift x₀ y')` using `hCp _ _ _ ⟨hUm _, h1⟩`. Establish `ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y'))` using `sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))`. Establish `hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y')`. Use function extensionality and compare the values at `q`.

Simplify using `[cj]`. Simplify using `only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]`. Rewrite using `[affCoord_eq_of_orbit p ho, affCoord_cj, hst]`.
-/
theorem conj_analytic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  intro K _ ι _ e X _ A P U lift hL c hc hcc j k w hw
  obtain ⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩ := hL
  obtain ⟨hw1, hw2⟩ := hw
  have hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source := hw2
  generalize hx₀ : (A.chart j).symm w = x₀ at hw2'
  generalize hx₁ : c x₀ = x₁ at hw2'
  choose p hp using (hM x₁ x₁ (hUm x₁)).1
  have hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0 := fun b =>
    ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)
  have hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁ := (A.chart k).left_inv hw2'
  have hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁) := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩
    · simpa [hsym₁] using hp b
  have hker := hIm x₁ p hp k hw2'
  have hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩
    · simpa [hx₀] using hp0 b
  have hsc : ContinuousAt (A.chart j).symm w := (A.chart j).continuousAt_symm hw1
  have hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w := hcc.continuousAt.comp hsc
  have hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w := by
    have h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w)) := by
      rw [hx₀, hx₁]; exact (A.chart k).continuousAt hw2'
    exact continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)
  have hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁) := by
    rw [hx₀, hx₁]
  have e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀ :=
    hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))
  have e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁ :=
    hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by
      change c ((A.chart j).symm w) ∈ _
      rw [hx₀, hx₁]; exact ⟨hw2', hUm x₁⟩))
  refine GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z))))
    (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star)
    (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_
  · rw [hFw]; exact analyticAt_star_comp hψ
  · rw [hFw]; exact ker_fderiv_star_comp hψ.differentiableAt hker
  · filter_upwards [e1, e2] with y h1 h2
    obtain ⟨h2s, h2u⟩ := h2
    generalize hy' : (A.chart j).symm y = y' at h1 h2s h2u
    have ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y')) := hCp _ _ _ ⟨h2u, hUm _⟩
    have ho2 : SameOrbit (lift y' y') (lift x₀ y') := hCp _ _ _ ⟨hUm _, h1⟩
    have ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y')) :=
      sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))
    have hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y') := by
      funext q; simp [cj]
    simp only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]
    rw [affCoord_eq_of_orbit p ho, affCoord_cj, hst]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
