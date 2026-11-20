import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN`. Take `⟨U, hUsub, hUo, h1U⟩` from `mem_nhds_iff.1 hN`. Take `⟨h, h1, h0, hcs, hrange⟩` from `exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl (Set.disjoint_singleton_left.2 fun h => h h1U)`. Establish `hnn : ∀ g, 0 ≤ h g` using `fun g => (hrange g).1`. Use `set c : ℝ := ∫ g, h g ∂μ with hc`.

Establish `hcpos : 0 < c` using `h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)`. Set `k : G → ℝ` to `fun g => c⁻¹ * h g`. Establish `hkc : Continuous k` using `continuous_const.mul h.continuous`. Establish `hkcs : HasCompactSupport k`. Establish `: k = (fun _ => c⁻¹) * (h : G → ℝ)` using `rfl`.

Rewrite using `[this]`. Conclude with `hcs.mul_left`. Establish `hknn : ∀ g, 0 ≤ k g` using `fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)`. Establish `hkint : Integrable k μ` using `hkc.integrable_of_hasCompactSupport hkcs`. Establish `hk1 : ∫ g, k g ∂μ = 1`.

Simplify using `only [k]`. Rewrite using `[integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']`. Set `f : CompactlySupportedContinuousMap G ℂ` to `⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩`. Establish `hfg : ∀ g, f g = (k g : ℂ)` using `fun _ => rfl`. Use `⟨f, fun v r hr => ?_⟩` and prove the remaining obligations.

Establish `hint1 : Integrable (fun g => f g • π g v) μ` using `(f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right`. Establish `hint2 : Integrable (fun g => f g • v) μ` using `(f.continuous.smul continuous_const).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right`. Establish `hv : ∫ g, f g • v ∂μ = v`. Rewrite using `[integral_smul_const]`. Simplify using `only [hfg]`.

Establish `: ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ)`. Rewrite using `[← hk1]`. Conclude with `integral_ofReal`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ`. Simplify using `only [smul_sub]`. Rewrite using `[integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]`. Establish `hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ`. Use `norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]`. Distinguish the cases in `hg : g ∈ U`. Conclude with `mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)`. Establish `: k g = 0`. Simplify using `only [k]`.

Rewrite using `[h0 hg]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[key]`.

Rewrite `hbound` using `[integral_mul_const, hk1, one_mul]`. Conclude with `hbound`.
-/
theorem UpperTheory.exists_approximate_identity_integrated :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (N : Set G), N ∈ 𝓝 (1 : G) → ∃ f : CompactlySupportedContinuousMap G ℂ, ∀ (v : H) (r : ℝ), (∀ g ∈ N, ‖π g v - v‖ ≤ r) → ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ r := by
  intro G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hN
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  let k : G → ℝ := fun g => c⁻¹ * h g
  have hkc : Continuous k := continuous_const.mul h.continuous
  have hkcs : HasCompactSupport k := by
    have : k = (fun _ => c⁻¹) * (h : G → ℝ) := rfl
    rw [this]
    exact hcs.mul_left
  have hknn : ∀ g, 0 ≤ k g := fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)
  have hkint : Integrable k μ := hkc.integrable_of_hasCompactSupport hkcs
  have hk1 : ∫ g, k g ∂μ = 1 := by
    simp only [k]
    rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (k g : ℂ) := fun _ => rfl
  refine ⟨f, fun v r hr => ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ) := by
      rw [← hk1]; exact integral_ofReal
    rw [this]
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ := by
    refine norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)
    · have : k g = 0 := by
        simp only [k]
        rw [h0 hg]
        simp
      rw [this]
      simp
  rw [key]
  rw [integral_mul_const, hk1, one_mul] at hbound
  exact hbound
