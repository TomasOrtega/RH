import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

set_option synthInstance.maxHeartbeats 400000

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Set `f : RightCosetSpace (Gam K n) → ℂ` to `fun x => φ x.out`. Establish `hf : ∀ g, f (mk (Gam K n) g) = φ g` using `fun g => by`. Take `⟨γ, hγ⟩` from `(mk_eq_mk_iff (Γ := Gam K n) (g := (mk (Gam K n) g).out) (h := g)).1 (Quotient.out_eq _)`. Express the relevant statement in the definitionally equal form `φ _ = _`.

Rewrite using `[← hγ]`. Conclude with `hi γ γ.2 g`. Establish `hfc : Continuous f`. Rewrite using `[(isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff]`. Establish `: f ∘ mk (Gam K n) = φ` using `funext hf`.

Rewrite using `[this]` and apply the resulting hypothesis. Establish `hm : MemLp f 2 (quotientMeasure (Gam K n) μ)` using `MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _)`. Use `⟨hm.toLp f, ?_⟩` and prove the remaining obligations. Establish `h1` using `hm.coeFn_toLp`. Establish `h2 : ∀ᵐ y ∂μ.restrict (fundamentalDomain (Gam K n)), (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)` using `ae_of_ae_map (measurable_mk (Gam K n)).aemeasurable h1`.

Establish `hF` using `isFundamentalDomain_fundamentalDomain (Gam K n) μ`. Establish `h3 : μ {y | ¬ (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)} = 0`. Use `hF.measure_zero_of_invariant _ (fun γ => ?_) ?_` and prove the remaining obligations. Use extensionality with `y`. Simplify using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Rewrite `h2` using `[ae_restrict_iff' (measurableSet_fundamentalDomain (Gam K n)), ae_iff]`. Use `measure_mono_null (fun y hy => ?_) h2` and prove the remaining obligations. Conclude with `fun h => hy.1 (h hy.2)`. Establish `h4 : ∀ᵐ y ∂μ, (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)` using `ae_iff.2 h3`. Use `filter_upwards [h4] with y hy`.

Rewrite using `[hy, hf]`.
-/
private theorem exists_rep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (φ : G1 K n → ℂ) (hc : Continuous φ) (hi : ∀ γ ∈ Gam K n, ∀ g, φ (γ * g) = φ g) (C : ℝ) (hC : ∀ g, ‖φ g‖ ≤ C) :
    ∃ v : L2 μ, Reps μ v φ := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let f : RightCosetSpace (Gam K n) → ℂ := fun x => φ x.out
  have hf : ∀ g, f (mk (Gam K n) g) = φ g := fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n) (g := (mk (Gam K n) g).out) (h := g)).1 (Quotient.out_eq _)
    change φ _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  have hfc : Continuous f := by
    rw [(isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff]
    have : f ∘ mk (Gam K n) = φ := funext hf
    rwa [this]
  have hm : MemLp f 2 (quotientMeasure (Gam K n) μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _)
  refine ⟨hm.toLp f, ?_⟩
  have h1 := hm.coeFn_toLp
  have h2 : ∀ᵐ y ∂μ.restrict (fundamentalDomain (Gam K n)), (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) :=
    ae_of_ae_map (measurable_mk (Gam K n)).aemeasurable h1
  have hF := isFundamentalDomain_fundamentalDomain (Gam K n) μ
  have h3 : μ {y | ¬ (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)} = 0 := by
    refine hF.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    · rw [ae_restrict_iff' (measurableSet_fundamentalDomain (Gam K n)), ae_iff] at h2
      refine measure_mono_null (fun y hy => ?_) h2
      exact fun h => hy.1 (h hy.2)
  have h4 : ∀ᵐ y ∂μ, (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) := ae_iff.2 h3
  filter_upwards [h4] with y hy
  rw [hy, hf]

/- English proof (translation)
Rewrite using `[L2.inner_def, integral_quotientMeasure]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae hw] with y h2`. Rewrite using `[h2, RCLike.inner_apply, mul_comm]`.
-/
private theorem orth {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} (u : L2 μ) {w : L2 μ}
    {ψ : G1 K n → ℂ} (hw : Reps μ w ψ) :
    ∫ m, conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) * ψ m ∂fd μ = ⟪u, w⟫_ℂ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hw] with y h2
  rw [h2, RCLike.inner_apply, mul_comm]

/- English proof (translation)
Use `continuous_parametric_integral_of_continuous (μ := μ) (f := fun y g => w g * Φ (y, g)) ((hw.comp continuous_snd).mul hΦ) hwc.isCompact` as an intermediate fact. Use `this.congr fun y => setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_` and prove the remaining obligations. Rewrite using `[image_eq_zero_of_notMem_tsupport hg, zero_mul]`.
-/
private theorem contInt {Y G : Type} [TopologicalSpace Y] [FirstCountableTopology Y] [LocallyCompactSpace Y]
    [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
    [IsLocallyFiniteMeasure μ] {w : G → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) {Φ : Y × G → ℂ}
    (hΦ : Continuous Φ) : Continuous fun y => ∫ g, w g * Φ (y, g) ∂μ := by
  have := continuous_parametric_integral_of_continuous (μ := μ) (f := fun y g => w g * Φ (y, g))
    ((hw.comp continuous_snd).mul hΦ) hwc.isCompact
  refine this.congr fun y => setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_
  rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

/- English proof (translation)
Establish `hwi : Integrable w μ` using `hw.integrable_of_hasCompactSupport hwc`. Take `⟨v, hv⟩` from `exists_rep μ₂ (fun m => ∫ g, w g * Φ (m, g) ∂μ) (contInt μ hw hwc hΦ) (fun γ hγ m => by simp only [hi γ hγ]) (∫ g, ‖w g‖ * C ∂μ) fun m => norm_integral_le_of_norm_le (hwi.norm.mul_const C) (Eventually.of_forall fun g => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))`. Use `⟨v, ?_, hv⟩` and prove the remaining obligations.

Use `haveI := hτ.completeSpace_coe`. Rewrite using `[← τ.orthogonal_orthogonal, Submodule.mem_orthogonal]`. Introduce `u hu`. Use `haveI := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ₂`. Establish `hu1 : Integrable (fun m => (u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) (fd μ₂)` using `((Lp.memLp u).integrable one_le_two).comp_measurable (measurable_mk _)`.

Establish `hu2 : Integrable (fun m => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m))) (fd μ₂)` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu1`. Use `haveI : BorelSpace (G1 K n × G1 K N) := Prod.borelSpace`. Establish `hI : Integrable (fun p : G1 K n × G1 K N => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) p.1)) * w p.2 * Φ p) ((fd μ₂).prod μ)` using `(hu2.mul_prod hwi).mul_bdd hΦ.aestronglyMeasurable (Eventually.of_forall hC)`. Rewrite using `[← orth u hv]`. Simplify using `only [← integral_const_mul, ← mul_assoc]`.

Rewrite using `[integral_integral_swap (f := fun m g => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) * w g * Φ (m, g)) hI]`. Use `integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Take `⟨v', hv', h⟩` from `hr g`. Use `orth u h` as an intermediate fact. Rewrite `this` using `[Submodule.inner_left_of_mem_orthogonal hv' hu]`.

Simplify using `only [mul_comm _ (w g), mul_assoc, integral_const_mul, this, mul_zero, Pi.zero_apply]`.
-/
private theorem slice_int {K : Type} [Field K] [NumberField K] {n N : ℕ} (μ : Measure (G1 K N)) [μ.IsHaarMeasure]
    (μ₂ : Measure (G1 K n)) [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)) (hτ : IsClosed (τ : Set (L2 μ₂)))
    {w : G1 K N → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) {Φ : G1 K n × G1 K N → ℂ} (hΦ : Continuous Φ)
    {C : ℝ} (hC : ∀ p, ‖Φ p‖ ≤ C) (hi : ∀ γ ∈ Gam K n, ∀ m g, Φ (γ * m, g) = Φ (m, g))
    (hr : ∀ g, ∃ v ∈ τ, Reps μ₂ v fun m => Φ (m, g)) : ∃ v ∈ τ, Reps μ₂ v fun m => ∫ g, w g * Φ (m, g) ∂μ := by
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hwc
  obtain ⟨v, hv⟩ := exists_rep μ₂ (fun m => ∫ g, w g * Φ (m, g) ∂μ) (contInt μ hw hwc hΦ)
    (fun γ hγ m => by simp only [hi γ hγ]) (∫ g, ‖w g‖ * C ∂μ) fun m =>
      norm_integral_le_of_norm_le (hwi.norm.mul_const C) (Eventually.of_forall fun g => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  refine ⟨v, ?_, hv⟩
  haveI := hτ.completeSpace_coe
  rw [← τ.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  haveI := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ₂
  have hu1 : Integrable (fun m => (u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) (fd μ₂) :=
    ((Lp.memLp u).integrable one_le_two).comp_measurable (measurable_mk _)
  have hu2 : Integrable (fun m => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m))) (fd μ₂) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu1
  haveI : BorelSpace (G1 K n × G1 K N) := Prod.borelSpace
  have hI : Integrable (fun p : G1 K n × G1 K N =>
      conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) p.1)) * w p.2 * Φ p) ((fd μ₂).prod μ) :=
    (hu2.mul_prod hwi).mul_bdd hΦ.aestronglyMeasurable (Eventually.of_forall hC)
  rw [← orth u hv]
  simp only [← integral_const_mul, ← mul_assoc]
  rw [integral_integral_swap (f := fun m g => conj ((u : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) m)) * w g * Φ (m, g)) hI]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun g => ?_)
  obtain ⟨v', hv', h⟩ := hr g
  have := orth u h
  rw [Submodule.inner_left_of_mem_orthogonal hv' hu] at this
  simp only [mul_comm _ (w g), mul_assoc, integral_const_mul, this, mul_zero, Pi.zero_apply]

/- English proof (translation)
Establish `e1 : ∀ k, e k * ∫ g, a g * Θ (k * g) ∂μ = ∫ g, e k * a (k⁻¹ * g) * Θ g ∂μ` using `fun k => by`. Rewrite using `[← integral_const_mul, ← integral_mul_left_eq_self _ k⁻¹]`. Simplify using `only [mul_inv_cancel_left, mul_assoc]`. Establish `hc : Continuous fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2` using `by fun_prop`. Establish `hI : Integrable (fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2) (ν.prod μ)`.

Use `(hc.continuousOn.integrableOn_compact (hU.prod (hU.mul hac.isCompact))).integrable_of_ae_notMem_eq_zero ?_` and prove the remaining obligations. Use `filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν] with p hp hn`. Establish `: a (p.1⁻¹ * p.2) = 0` using `by_contra fun h0 => hn ⟨hp, p.1, hp, _, subset_tsupport _ h0, mul_inv_cancel_left _ _⟩`. Rewrite using `[this, mul_zero, zero_mul]`. Simplify using `only [e1]`.

Rewrite using `[integral_integral_swap (f := fun k g => e k * a (k⁻¹ * g) * Θ g) hI]`. Simplify using `only [integral_mul_const, h]`.
-/
private theorem fix_int {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) {e a Θ : G → ℂ} (he : Continuous e) (ha : Continuous a)
    (hac : HasCompactSupport a) (hΘ : Continuous Θ) (h : ∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g) :
    ∫ k, e k * ∫ g, a g * Θ (k * g) ∂μ ∂ν = ∫ g, a g * Θ g ∂μ := by
  have e1 : ∀ k, e k * ∫ g, a g * Θ (k * g) ∂μ = ∫ g, e k * a (k⁻¹ * g) * Θ g ∂μ := fun k => by
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ k⁻¹]
    simp only [mul_inv_cancel_left, mul_assoc]
  have hc : Continuous fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2 := by fun_prop
  have hI : Integrable (fun p : G × G => e p.1 * a (p.1⁻¹ * p.2) * Θ p.2) (ν.prod μ) := by
    refine (hc.continuousOn.integrableOn_compact (hU.prod (hU.mul hac.isCompact))).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν] with p hp hn
    have : a (p.1⁻¹ * p.2) = 0 := by_contra fun h0 =>
      hn ⟨hp, p.1, hp, _, subset_tsupport _ h0, mul_inv_cancel_left _ _⟩
    rw [this, mul_zero, zero_mul]
  simp only [e1]
  rw [integral_integral_swap (f := fun k g => e k * a (k⁻¹ * g) * Θ g) hI]
  simp only [integral_mul_const, h]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ D h₁ h₂ a χ f ha hχ hf hD`. Take `⟨hH1, hH2, -, hHc, hH5⟩` from `hpSpec (K := K)`. Take `⟨-, hmul, -, hlv, -⟩` from `blkLaws (K := K)`. Take `⟨hU, hUK, -⟩` from `typeFin D`. Take `⟨hfc, ⟨C, hC⟩, hfu, hfr, hfs⟩` from `(secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hD).1 hf`.

Establish `hS` using `secFun μ₂ τ₁ τ₂ D h₁ h₂ f hf hD`. Set `ψ : ℝ → ℂ` to `fun s => χ s * Complex.exp (2 * (s : ℂ))`. Establish `hψ : Continuous ψ`. Simplify using `only [ψ]`. Use `fun_prop`.

Establish `hT : ∀ x, tChi μ a χ f x = ∫ g, a g * (ψ (HH (x * g) - HH x) * f (x * g)) ∂μ` using `fun x => by`. Simplify using `only [tChi, ψ, mul_assoc]`. Establish `hlv0 : ∀ m₁ m₂ t y, HH (lv m₁ m₂ t * y) = t + HH (y : G1 K (2 + 2))` using `fun m₁ m₂ t y => by`. Use `hH1 0 m₁ m₂ t y` as an intermediate fact. Rewrite `this` using `[show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]`. Then use the resulting hypothesis.

Establish `hfix : D.Fix (tChi μ a χ f)` using `fun x => by haveI := D.prob`. Rewrite using `[hT x, ← fix_int μ D.ν hU D.supp D.cont (a := fun g => a g) a.continuous a.hasCompactSupport (Θ := fun g => ψ (HH (x * g) - HH x) * f (x * g)) ((hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const)).mul (hfc.comp (continuous_const.mul continuous_id))) fu …`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [D.supp] with k hk`. Rewrite using `[hT, (hH2 k (hUK hk)).2]`.

Simplify using `only [mul_assoc]`. Establish `hsl : ∀ m₁ m₂ x, tChi μ a χ f (lv m₁ m₂ 0 * x) = ∫ g, (a g * ψ (HH (x * g) - HH x)) * f (lv m₁ m₂ 0 * (x * g)) ∂μ` using `fun m₁ m₂ x => by`. Simplify using `only [hT, mul_assoc, hlv0, zero_add]`. Establish `hw : ∀ x, Continuous fun g => a g * ψ (HH (x * g) - HH x)` using `fun x => a.continuous.mul (hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const))`. Use `⟨(secCrit μ₂ τ₁ τ₂ D h₁ h₂ _ hfix).2 ⟨?_, ?_, fun X x => ?_, fun t x => ?_, fun x => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩, hfix⟩` and prove the remaining obligations.

Use `(contInt μ (w := fun g => a g) a.continuous a.hasCompactSupport (Φ := fun p : G1 K (2 + 2) × G1 K (2 + 2) => ψ (HH (p.1 * p.2) - HH p.1) * f (p.1 * p.2)) ?_).congr fun x => (hT x).symm` and prove the remaining obligations. Conclude with `(hψ.comp ((hHc.comp continuous_mul).sub (hHc.comp continuous_fst))).mul (hfc.comp continuous_mul)`. Take `⟨R, hR⟩` from `hH5 _ a.hasCompactSupport.isCompact`. Take `⟨M, hM⟩` from `(isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hψ.continuousOn`. Use `⟨∫ g, ‖a g‖ * (M * C) ∂μ, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hT]`. Use `norm_integral_le_of_norm_le ((a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport).norm.mul_const _) (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : a g = 0`. Simplify using `[h0]`. Establish `h1` using `hM _ (abs_le.1 (hR x g (subset_tsupport _ h0)))`.

Rewrite using `[norm_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul h1 (hC _) (norm_nonneg _) ((norm_nonneg _).trans h1)) (norm_nonneg _)`. Establish `h0 : ∀ y, HH (nn X * y) = HH y` using `fun y => by`. Use `hH1 X 1 1 0 y` as an intermediate fact. Rewrite `this` using `[(blkLaws (K := K)).2.2.1, mul_one, zero_add]`. Then use the resulting hypothesis.

Simplify using `only [hT, mul_assoc, h0, hfu]`. Simplify using `only [hT, mul_assoc, hlv0, hfr, add_sub_add_left_eq_sub]`. Simplify using `only [hsl]`. Use `slice_int μ μ₂ τ₁ h₁.closed (hw x) a.hasCompactSupport.mul_right (Φ := fun p => f (lv p.1 m₂ 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).1 m₂` and prove the remaining obligations. Establish `: Continuous fun p : G1 K 2 × G1 K (2 + 2) => (p.1, m₂, (0 : ℝ))` using `by fun_prop`.

Conclude with `hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))`. Establish `e : lv (γ * m) m₂ 0 = lv γ 1 0 * lv m m₂ 0` using `by rw [hmul, one_mul, add_zero]`. Use `hS.rat (lv γ 1 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, ⟨γ, hγ⟩, 1, by` as an intermediate fact. Rewrite using `[show (nn (0 : unipLattice K (2 + 2) 2).1 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]`. Use the proof step `rfl⟩)`.

Simplify using `only [e, mul_assoc, this]`. Simplify using `only [hsl]`. Use `slice_int μ μ₂ τ₂ h₂.closed (hw x) a.hasCompactSupport.mul_right (Φ := fun p => f (lv m₁ p.1 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).2 m₁` and prove the remaining obligations. Establish `: Continuous fun p : G1 K 2 × G1 K (2 + 2) => (m₁, p.1, (0 : ℝ))` using `by fun_prop`. Conclude with `hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))`.

Establish `e : lv m₁ (γ * m) 0 = lv 1 γ 0 * lv m₁ m 0` using `by rw [hmul, one_mul, add_zero]`. Use `hS.rat (lv 1 γ 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by` as an intermediate fact. Rewrite using `[show (nn (0 : unipLattice K (2 + 2) 2).1 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]`. Use the proof step `rfl⟩)`. Simplify using `only [e, mul_assoc, this]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tChiSec :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ (a : CC K (2 + 2)) (χ : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ),
      D.Hecke a → Continuous χ → IsSec τ₁ τ₂ f → D.Fix f → IsSec τ₁ τ₂ (tChi μ a χ f) ∧ D.Fix (tChi μ a χ f) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ D h₁ h₂ a χ f ha hχ hf hD
  obtain ⟨hH1, hH2, -, hHc, hH5⟩ := hpSpec (K := K)
  obtain ⟨-, hmul, -, hlv, -⟩ := blkLaws (K := K)
  obtain ⟨hU, hUK, -⟩ := typeFin D
  obtain ⟨hfc, ⟨C, hC⟩, hfu, hfr, hfs⟩ := (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hD).1 hf
  have hS := secFun μ₂ τ₁ τ₂ D h₁ h₂ f hf hD
  let ψ : ℝ → ℂ := fun s => χ s * Complex.exp (2 * (s : ℂ))
  have hψ : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hT : ∀ x, tChi μ a χ f x = ∫ g, a g * (ψ (HH (x * g) - HH x) * f (x * g)) ∂μ := fun x => by
    simp only [tChi, ψ, mul_assoc]
  have hlv0 : ∀ m₁ m₂ t y, HH (lv m₁ m₂ t * y) = t + HH (y : G1 K (2 + 2)) := fun m₁ m₂ t y => by
    have := hH1 0 m₁ m₂ t y
    rwa [show (nn 0 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul] at this
  have hfix : D.Fix (tChi μ a χ f) := fun x => by
    haveI := D.prob
    rw [hT x, ← fix_int μ D.ν hU D.supp D.cont (a := fun g => a g) a.continuous a.hasCompactSupport
      (Θ := fun g => ψ (HH (x * g) - HH x) * f (x * g))
      ((hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const)).mul
        (hfc.comp (continuous_const.mul continuous_id))) fun g => (ha g).1]
    refine integral_congr_ae ?_
    filter_upwards [D.supp] with k hk
    rw [hT, (hH2 k (hUK hk)).2]
    simp only [mul_assoc]
  have hsl : ∀ m₁ m₂ x, tChi μ a χ f (lv m₁ m₂ 0 * x) =
      ∫ g, (a g * ψ (HH (x * g) - HH x)) * f (lv m₁ m₂ 0 * (x * g)) ∂μ := fun m₁ m₂ x => by
    simp only [hT, mul_assoc, hlv0, zero_add]
  have hw : ∀ x, Continuous fun g => a g * ψ (HH (x * g) - HH x) := fun x =>
    a.continuous.mul (hψ.comp ((hHc.comp (continuous_const.mul continuous_id)).sub continuous_const))
  refine ⟨(secCrit μ₂ τ₁ τ₂ D h₁ h₂ _ hfix).2 ⟨?_, ?_, fun X x => ?_, fun t x => ?_, fun x => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩,
    hfix⟩
  · refine (contInt μ (w := fun g => a g) a.continuous a.hasCompactSupport (Φ := fun p : G1 K (2 + 2) × G1 K (2 + 2) =>
      ψ (HH (p.1 * p.2) - HH p.1) * f (p.1 * p.2)) ?_).congr fun x => (hT x).symm
    exact (hψ.comp ((hHc.comp continuous_mul).sub (hHc.comp continuous_fst))).mul (hfc.comp continuous_mul)
  · obtain ⟨R, hR⟩ := hH5 _ a.hasCompactSupport.isCompact
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hψ.continuousOn
    refine ⟨∫ g, ‖a g‖ * (M * C) ∂μ, fun x => ?_⟩
    rw [hT]
    refine norm_integral_le_of_norm_le
      ((a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport).norm.mul_const _) (Eventually.of_forall fun g => ?_)
    by_cases h0 : a g = 0
    · simp [h0]
    · have h1 := hM _ (abs_le.1 (hR x g (subset_tsupport _ h0)))
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (hC _) (norm_nonneg _) ((norm_nonneg _).trans h1)) (norm_nonneg _)
  · have h0 : ∀ y, HH (nn X * y) = HH y := fun y => by
      have := hH1 X 1 1 0 y
      rwa [(blkLaws (K := K)).2.2.1, mul_one, zero_add] at this
    simp only [hT, mul_assoc, h0, hfu]
  · simp only [hT, mul_assoc, hlv0, hfr, add_sub_add_left_eq_sub]
  · simp only [hsl]
    refine slice_int μ μ₂ τ₁ h₁.closed (hw x) a.hasCompactSupport.mul_right
      (Φ := fun p => f (lv p.1 m₂ 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).1 m₂
    · have : Continuous fun p : G1 K 2 × G1 K (2 + 2) => (p.1, m₂, (0 : ℝ)) := by fun_prop
      exact hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))
    · have e : lv (γ * m) m₂ 0 = lv γ 1 0 * lv m m₂ 0 := by rw [hmul, one_mul, add_zero]
      have := hS.rat (lv γ 1 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, ⟨γ, hγ⟩, 1, by
        rw [show (nn (0 : unipLattice K (2 + 2) 2).1 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]; rfl⟩)
      simp only [e, mul_assoc, this]
  · simp only [hsl]
    refine slice_int μ μ₂ τ₂ h₂.closed (hw x) a.hasCompactSupport.mul_right
      (Φ := fun p => f (lv m₁ p.1 0 * (x * p.2))) ?_ (fun _ => hC _) (fun γ hγ m g => ?_) fun g => (hfs (x * g)).2 m₁
    · have : Continuous fun p : G1 K 2 × G1 K (2 + 2) => (m₁, p.1, (0 : ℝ)) := by fun_prop
      exact hfc.comp ((hlv.comp this).mul (continuous_const.mul continuous_snd))
    · have e : lv m₁ (γ * m) 0 = lv 1 γ 0 * lv m₁ m 0 := by rw [hmul, one_mul, add_zero]
      have := hS.rat (lv 1 γ 0) (((pkLaws (K := K)).2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by
        rw [show (nn (0 : unipLattice K (2 + 2) 2).1 : G1 K (2 + 2)) = 1 from unipOne_zero 2, one_mul]; rfl⟩)
      simp only [e, mul_assoc, this]
