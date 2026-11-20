import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisAvg

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/- English proof (translation)
Distinguish the cases in `h0 : φ κ = 0`. Simplify using `[h0]`. Take `⟨r, v, hr, hv, rfl, hn⟩` from `hN κ h0`. Establish `hM0 : 0 < M` using `by linarith`. Establish `hcr : ‖c r‖ = 1` using `hc _ hr`.

Establish `hφ : φ (r * v) = c r * φ v` using `hL r v hr`. Establish `hnorm : ‖φ (r * v)‖ = ‖φ v‖` using `by rw [hφ, norm_mul, hcr, one_mul]`. Establish `hwr : c r • ρ r w = w` using `hw r hr`. Take `⟨u, hu⟩ : ∃ u, u = ρ v w - w` from `⟨_, rfl⟩`. Establish `hub : ‖u‖ ≤ ‖w‖ / (4 * M)`.

Establish `h1 : u = (ρ v - 1) w` using `by simp [hu]`. Establish `hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M)` using `hv`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4`.

Rewrite using `[norm_smul, hcr, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hM r`. Use `_ = ‖w‖ / 4 := by field_simp`. Establish `hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w = (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)`.

Establish `h2 : ρ v w = w + u` using `by simp [hu]`. Establish `h3 : ρ (r * v) w = ρ r w + ρ r u`. Rewrite using `[map_mul, ContinuousLinearMap.mul_apply, h2, map_add]`. Rewrite using `[hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hexp, hnorm]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_smul]`. Use `_ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr`.

Use `_ = ‖φ v‖ * ‖w‖ / 2 := by ring`.
-/
theorem pointwise_bound {K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {φ : K → ℂ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ κ, ‖ρ κ‖ ≤ M) (hc : ∀ p ∈ P, ‖c p‖ = 1) (hL : Law K P c φ)
    (hN : Near K P {v | ‖ρ v - 1‖ ≤ 1 / (4 * M)} φ) {w : W} (hw : w ∈ secSp K P c ρ) (κ : K) :
    ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2 := by
  by_cases h0 : φ κ = 0
  · simp [h0]
  obtain ⟨r, v, hr, hv, rfl, hn⟩ := hN κ h0
  have hM0 : 0 < M := by linarith
  have hcr : ‖c r‖ = 1 := hc _ hr
  have hφ : φ (r * v) = c r * φ v := hL r v hr
  have hnorm : ‖φ (r * v)‖ = ‖φ v‖ := by rw [hφ, norm_mul, hcr, one_mul]
  have hwr : c r • ρ r w = w := hw r hr
  obtain ⟨u, hu⟩ : ∃ u, u = ρ v w - w := ⟨_, rfl⟩
  have hub : ‖u‖ ≤ ‖w‖ / (4 * M) := by
    have h1 : u = (ρ v - 1) w := by simp [hu]
    have hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M) := hv
    rw [h1]
    calc ‖(ρ v - 1) w‖ ≤ ‖ρ v - 1‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (4 * M) * ‖w‖ := by gcongr
      _ = ‖w‖ / (4 * M) := by ring
  have hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4 := by
    rw [norm_smul, hcr, one_mul]
    calc ‖ρ r u‖ ≤ ‖ρ r‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (‖w‖ / (4 * M)) := by
          gcongr
          exact hM r
      _ = ‖w‖ / 4 := by field_simp
  have hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w =
      (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u) := by
    have h2 : ρ v w = w + u := by simp [hu]
    have h3 : ρ (r * v) w = ρ r w + ρ r u := by
      rw [map_mul, ContinuousLinearMap.mul_apply, h2, map_add]
    rw [hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]
    abel
  rw [hexp, hnorm]
  calc ‖(φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)‖
      ≤ ‖φ v - ((‖φ v‖ : ℝ) : ℂ)‖ * ‖w‖ + ‖φ v‖ * ‖c r • ρ r u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr
    _ = ‖φ v‖ * ‖w‖ / 2 := by ring

/- English proof (translation)
Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Establish `hint : Integrable (fun κ => φ κ • ρ κ) μ` using `(hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hint2 : Integrable (fun κ => ‖φ κ‖) μ` using `hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hint3 : Integrable (fun κ => φ κ • ρ κ w) μ`. Use `hint.apply_continuousLinearMap w` as an intermediate fact.

Conclude with `this`. Establish `hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ` using `(hint2.ofReal (𝕜 := ℂ)).smul_const w`. Establish `e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ` using `ContinuousLinearMap.integral_apply hint w`. Establish `e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ`. Rewrite using `[integral_smul_const, integral_complex_ofReal]`.

Rewrite using `[e1, e2, ← integral_sub hint3 hint4]`. Establish `e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ`. Rewrite using `[integral_div, integral_mul_const]`. Rewrite using `[e3]`. Conclude with `norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)`.
-/
theorem avg_sub_bound [FiniteDimensional ℂ W] {K : Subgroup G} [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {φ : K → ℂ} (hφ : Continuous φ) (w : W)
    (h : ∀ κ, ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2) :
    ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hint : Integrable (fun κ => φ κ • ρ κ) μ :=
    (hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun κ => ‖φ κ‖) μ :=
    hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun κ => φ κ • ρ κ w) μ := by
    have := hint.apply_continuousLinearMap w
    exact this
  have hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ :=
    (hint2.ofReal (𝕜 := ℂ)).smul_const w
  have e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ := ContinuousLinearMap.integral_apply hint w
  have e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ := by
    rw [integral_smul_const, integral_complex_ofReal]
  rw [e1, e2, ← integral_sub hint3 hint4]
  have e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ := by
    rw [integral_div, integral_mul_const]
  rw [e3]
  exact norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)

/- English proof (translation)
Use `hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_` and prove the remaining obligations. Simplify using `[h1]`.
-/
theorem mass_pos {K : Subgroup G} [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [IsTopologicalGroup K] (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {φ : K → ℂ} (hφ : Continuous φ) (h1 : φ 1 = 1) : 0 < ∫ κ, ‖φ κ‖ ∂μ := by
  refine hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_
  simp [h1]

end Abstract

/- English proof (translation)
Introduce `hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI := hH`. Use `haveI := hP`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by`.

Take `⟨C, hC⟩` from `(isCompact_range hρ).isBounded.exists_norm_le`. Conclude with `⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩`. Establish `hM0 : 0 < M` using `by linarith`. Use `⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩` and prove the remaining obligations. Establish `ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0)`.

Establish `h5` using `hρ.tendsto (1 : K)`. Rewrite `h5` using `[map_one]`. Simplify using `using h5.sub_const 1`. Establish `h4 : (0 : ℝ) < 1 / (4 * M)` using `by positivity`. Use `filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv`.

Simplify using `using hv`. Introduce `φ hφ h1 hL hN`. Establish `hI : 0 < ∫ κ, ‖φ κ‖ ∂μ` using `mass_pos μ hφ h1`. Establish `hb : ∀ w ∈ secSp K P c ρ, ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2` using `fun w hw => avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)`. Establish `hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ` using `fun w => hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w`.

Set `T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ` to `((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w`. Establish `hinj : Function.Injective T`. Use `(injective_iff_map_eq_zero T).mpr fun w hw => ?_` and prove the remaining obligations. Establish `h0 : avg μ ρ φ (w : W) = 0` using `congrArg Subtype.val hw`. Establish `h6` using `hb w w.2`.

Rewrite `h6` using `[h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le]`. Establish `h7 : ‖(w : W)‖ = 0`. Establish `h8 : 0 ≤ ‖(w : W)‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `Subtype.ext (norm_eq_zero.mp h7)`.

Set `e` to `LinearEquiv.ofInjectiveEndo T hinj`. Use `⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (e.apply_symm_apply w)`.
-/
theorem avgInv_of_avgMem : AvgMem → AvgInv := by
  intro hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI := hH
  haveI := hP
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_range hρ).isBounded.exists_norm_le
    exact ⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩
  · have ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0) := by
      have h5 := hρ.tendsto (1 : K)
      rw [map_one] at h5
      simpa using h5.sub_const 1
    have h4 : (0 : ℝ) < 1 / (4 * M) := by positivity
    filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv
    simpa using hv
  · intro φ hφ h1 hL hN
    have hI : 0 < ∫ κ, ‖φ κ‖ ∂μ := mass_pos μ hφ h1
    have hb : ∀ w ∈ secSp K P c ρ,
        ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := fun w hw =>
      avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)
    have hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ := fun w =>
      hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w
    let T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ :=
      ((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun w hw => ?_
      have h0 : avg μ ρ φ (w : W) = 0 := congrArg Subtype.val hw
      have h6 := hb w w.2
      rw [h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le] at h6
      have h7 : ‖(w : W)‖ = 0 := by
        have h8 : 0 ≤ ‖(w : W)‖ := norm_nonneg _
        nlinarith
      exact Subtype.ext (norm_eq_zero.mp h7)
    let e := LinearEquiv.ofInjectiveEndo T hinj
    refine ⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply w)

end GlobalTheory.CompanionTheory.RgEisAvg
