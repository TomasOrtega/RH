import Mathlib
open Set Metric

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ F U hU hF K hK hKU h1 ε hε`. Use `set g : E × E → E →L[ℝ] E := fun q => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ E E) with hg`. Establish `hFd : ∀ q ∈ U, HasFDerivAt F (fderiv ℝ F q) q` using `fun q hq => ((hF.differentiableOn one_ne_zero q hq).differentiableAt (hU.mem_nhds hq)).hasFDerivAt`. Establish `hcont : ContinuousOn g U` using `(hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const`. Establish `hid : ∀ z ∈ K, g (z, 0) = ContinuousLinearMap.id ℝ E`.

Introduce `z hz`. Use extensionality with `η`. Establish `hc : HasDerivAt (fun s : ℝ => (z, s • η)) ((0 : E), η) 0`. Use `(hasDerivAt_const (0:ℝ) z).prodMk ((hasDerivAt_id (0:ℝ)).smul_const η)` as an intermediate fact. Simplify using `using this`.

Establish `hF0 : HasFDerivAt F (fderiv ℝ F (z, 0)) ((fun s : ℝ => (z, s • η)) 0)`. Simplify using `using hFd (z, 0) (hKU z hz)`. Establish `hcomp` using `hF0.comp_hasDerivAt (0:ℝ) hc`. Use `hcomp.unique (h1 z hz η)` as an intermediate fact. Simplify `this` using `[hg]`.

Establish `hKK : IsCompact (K ×ˢ ({0} : Set E))` using `hK.prod isCompact_singleton`. Establish `hKKU : K ×ˢ ({0} : Set E) ⊆ U`. Introduce and unpack `⟨z, w⟩ ⟨hz, hw⟩`. Simplify using `only [mem_singleton_iff] at hw`. Substitute `hw` using the available equality.

Conclude with `hKU z hz`. Take `⟨δ₀, hδ₀, hδ₀U⟩` from `hKK.exists_cthickening_subset_open hU hKKU`. Establish `hCc : IsCompact (cthickening δ₀ (K ×ˢ ({0} : Set E)))` using `hKK.cthickening`. Establish `huc` using `hCc.uniformContinuousOn_of_continuous (hcont.mono hδ₀U)`. Rewrite `huc` using `[Metric.uniformContinuousOn_iff]`.

Take `⟨δ₁, hδ₁, hδ₁'⟩` from `huc ε hε`. Use `⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (half_pos hδ₁), fun z η => g (z, η), ?_⟩` and prove the remaining obligations. Introduce `z hz η hη`. Establish `hη0 : ‖η‖ ≤ δ₀` using `hη.trans (min_le_left _ _)`. Establish `hη1 : ‖η‖ < δ₁` using `lt_of_le_of_lt (hη.trans (min_le_right _ _)) (half_lt_self hδ₁)`.

Establish `hdist : dist (z, η) (z, (0:E)) = ‖η‖`. Simplify using `[Prod.dist_eq, dist_eq_norm]`. Establish `hmemC : (z, η) ∈ cthickening δ₀ (K ×ˢ ({0} : Set E))` using `mem_cthickening_of_dist_le _ (z, 0) _ _ ⟨hz, rfl⟩ (hdist ▸ hη0)`. Establish `h0C : (z, (0:E)) ∈ cthickening δ₀ (K ×ˢ ({0} : Set E))` using `self_subset_cthickening _ ⟨hz, rfl⟩`. Establish `hmemU : (z, η) ∈ U` using `hδ₀U hmemC`.

Use `⟨hmemU, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hFd (z, η) hmemU).comp η (hasFDerivAt_prodMk_right z η)`. Use `hδ₁' (z, η) hmemC (z, 0) h0C (by rw [hdist]; exact hη1)` as an intermediate fact. Rewrite `this` using `[dist_eq_norm, hid z hz]`. Conclude with `this.le`.
-/
theorem fibre_fderiv_uniformly_near_id :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : E × E → E) (U : Set (E × E)), IsOpen U → ContDiffOn ℝ 1 F U → ∀ (K : Set E), IsCompact K → (∀ z ∈ K, (z, (0 : E)) ∈ U) → (∀ z ∈ K, ∀ η : E, HasDerivAt (fun s : ℝ => F (z, s • η)) η 0) → ∀ (ε : ℝ), 0 < ε → ∃ δ > 0, ∃ L : E → E → E →L[ℝ] E, ∀ z ∈ K, ∀ η : E, ‖η‖ ≤ δ → (z, η) ∈ U ∧ HasFDerivAt (fun η' => F (z, η')) (L z η) η ∧ ‖L z η - ContinuousLinearMap.id ℝ E‖ ≤ ε := by
  intro E _ _ _ F U hU hF K hK hKU h1 ε hε
  set g : E × E → E →L[ℝ] E := fun q => (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ E E) with hg
  have hFd : ∀ q ∈ U, HasFDerivAt F (fderiv ℝ F q) q := fun q hq =>
    ((hF.differentiableOn one_ne_zero q hq).differentiableAt (hU.mem_nhds hq)).hasFDerivAt
  have hcont : ContinuousOn g U :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const

  have hid : ∀ z ∈ K, g (z, 0) = ContinuousLinearMap.id ℝ E := by
    intro z hz
    ext η
    have hc : HasDerivAt (fun s : ℝ => (z, s • η)) ((0 : E), η) 0 := by
      have := (hasDerivAt_const (0:ℝ) z).prodMk ((hasDerivAt_id (0:ℝ)).smul_const η)
      simpa using this
    have hF0 : HasFDerivAt F (fderiv ℝ F (z, 0)) ((fun s : ℝ => (z, s • η)) 0) := by
      simpa using hFd (z, 0) (hKU z hz)
    have hcomp := hF0.comp_hasDerivAt (0:ℝ) hc
    have := hcomp.unique (h1 z hz η)
    simpa [hg] using this
  have hKK : IsCompact (K ×ˢ ({0} : Set E)) := hK.prod isCompact_singleton
  have hKKU : K ×ˢ ({0} : Set E) ⊆ U := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    simp only [mem_singleton_iff] at hw
    subst hw
    exact hKU z hz
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hKK.exists_cthickening_subset_open hU hKKU
  have hCc : IsCompact (cthickening δ₀ (K ×ˢ ({0} : Set E))) := hKK.cthickening
  have huc := hCc.uniformContinuousOn_of_continuous (hcont.mono hδ₀U)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := huc ε hε
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (half_pos hδ₁), fun z η => g (z, η), ?_⟩
  intro z hz η hη
  have hη0 : ‖η‖ ≤ δ₀ := hη.trans (min_le_left _ _)
  have hη1 : ‖η‖ < δ₁ := lt_of_le_of_lt (hη.trans (min_le_right _ _)) (half_lt_self hδ₁)
  have hdist : dist (z, η) (z, (0:E)) = ‖η‖ := by
    simp [Prod.dist_eq, dist_eq_norm]
  have hmemC : (z, η) ∈ cthickening δ₀ (K ×ˢ ({0} : Set E)) :=
    mem_cthickening_of_dist_le _ (z, 0) _ _ ⟨hz, rfl⟩ (hdist ▸ hη0)
  have h0C : (z, (0:E)) ∈ cthickening δ₀ (K ×ˢ ({0} : Set E)) :=
    self_subset_cthickening _ ⟨hz, rfl⟩
  have hmemU : (z, η) ∈ U := hδ₀U hmemC
  refine ⟨hmemU, ?_, ?_⟩
  · exact (hFd (z, η) hmemU).comp η (hasFDerivAt_prodMk_right z η)
  · have := hδ₁' (z, η) hmemC (z, 0) h0C (by rw [hdist]; exact hη1)
    rw [dist_eq_norm, hid z hz] at this
    exact this.le

end GlobalTheory
