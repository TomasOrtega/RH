import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AmpComm
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DiracSep

section General

open MeasureTheory GroundTheory.Automorphic
open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
The claim follows from `(hF.continuousOn.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero h0`.
-/
private theorem integrable_ae_cpt {X H : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup H] {m : Measure X} [IsFiniteMeasureOnCompacts m] {S : Set X} (hS : IsCompact S) {F : X → H}
    (hF : Continuous F) (h0 : ∀ᵐ x ∂m, x ∉ S → F x = 0) : Integrable F m :=
  (hF.continuousOn.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero h0

variable {ν : Measure G} [IsFiniteMeasure ν] {U : Subgroup G} {e : G → ℂ}

/- English proof (translation)
Use `integral_integral_swap (integrable_ae_cpt (hU.prod hU) hF ?_)` and prove the remaining obligations. Use `filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hs, (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hs] with q h1 h2 h`. Conclude with `absurd ⟨h1, h2⟩ h`.
-/
private theorem swap_cpt (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) : ∫ k, ∫ h, F k h ∂ν ∂ν = ∫ h, ∫ k, F k h ∂ν ∂ν := by
  refine integral_integral_swap (integrable_ae_cpt (hU.prod hU) hF ?_)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hs,
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hs] with q h1 h2 h
  exact absurd ⟨h1, h2⟩ h

/- English proof (translation)
Establish `h1 : ∫ k, e k * ∫ h, e h * φ (k * h) ∂ν ∂ν = ∫ k, ∫ h, e k * e (k⁻¹ * h) * φ h ∂ν ∂ν`. Use `integral_congr_ae (hs.mono fun k hk => ?_)` and prove the remaining obligations. Use `(hi k hk).integral_comp (MeasurableEquiv.mulLeft k).measurableEmbedding (fun h => e (k⁻¹ * h) * φ h)` as an intermediate fact. Simplify using `only [inv_mul_cancel_left] at this`. Simplify using `only [this, ← integral_const_mul, mul_assoc]`.

Rewrite using `[h1, swap_cpt hU hs (by fun_prop)]`. Use `integral_congr_ae (hs.mono fun k hk => ?_)` and prove the remaining obligations. Simplify using `only [integral_mul_const, hid k hk]`.
-/
private theorem idem_int (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) (he : Continuous e)
    (hid : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k) {φ : G → ℂ} (hφ : Continuous φ) :
    ∫ k, e k * ∫ h, e h * φ (k * h) ∂ν ∂ν = ∫ h, e h * φ h ∂ν := by
  have h1 : ∫ k, e k * ∫ h, e h * φ (k * h) ∂ν ∂ν = ∫ k, ∫ h, e k * e (k⁻¹ * h) * φ h ∂ν ∂ν := by
    refine integral_congr_ae (hs.mono fun k hk => ?_)
    have := (hi k hk).integral_comp (MeasurableEquiv.mulLeft k).measurableEmbedding (fun h => e (k⁻¹ * h) * φ h)
    simp only [inv_mul_cancel_left] at this
    simp only [this, ← integral_const_mul, mul_assoc]
  rw [h1, swap_cpt hU hs (by fun_prop)]
  refine integral_congr_ae (hs.mono fun k hk => ?_)
  simp only [integral_mul_const, hid k hk]

/- English proof (translation)
Use `continuous_parametric_integral_of_continuous (μ := ν) hF hU` as an intermediate fact. Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem hs]`. Then use the resulting hypothesis.
-/
private theorem cont_int (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) : Continuous fun g => ∫ k, F g k ∂ν := by
  have := continuous_parametric_integral_of_continuous (μ := ν) hF hU
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
  (μ : Measure G) [μ.IsHaarMeasure]

/- English proof (translation)
The claim follows from `integrable_ae_cpt hU (he.smul (π.continuous_orbit v)) (hs.mono fun _ h h' => absurd h h')`.
-/
private theorem int_orbit (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e) (v : H) :
    Integrable (fun k => e k • π k v) ν :=
  integrable_ae_cpt hU (he.smul (π.continuous_orbit v)) (hs.mono fun _ h h' => absurd h h')

/- English proof (translation)
Use `⟨⟨⟨fun x => ∫ k, F x k ∂ν, cont_int hU hs hF⟩, HasCompactSupport.intro hS fun x hx => ?_⟩, fun _ => rfl, fun v => ?_⟩` and prove the remaining obligations. Conclude with `integral_eq_zero_of_ae (hs.mono fun k hk => h0 x hx k hk)`. Rewrite using `[UnitaryRep.integrated_ccToL1_apply]`. Express the relevant statement in the definitionally equal form `∫ x, (∫ k, F x k ∂ν) • π x v ∂μ = _`. Simplify using `only [← integral_smul_const]`.

Use `integral_integral_swap (integrable_ae_cpt (hS.prod hU) (hF.smul ((π.continuous_orbit v).comp continuous_fst)) ?_)` and prove the remaining obligations. Use `filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs] with q h2 h`. Establish `: F q.1 q.2 = 0` using `h0 _ (fun h1 => h ⟨h1, h2⟩) _ h2`. Express the relevant statement in the definitionally equal form `F q.1 q.2 • π q.1 v = 0`. Rewrite using `[this, zero_smul]`.
-/
private theorem op_swap (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) {S : Set G} (hS : IsCompact S) (h0 : ∀ x ∉ S, ∀ k ∈ U, F x k = 0) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, F x k ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v = ∫ k, ∫ x, F x k • π x v ∂μ ∂ν := by
  refine ⟨⟨⟨fun x => ∫ k, F x k ∂ν, cont_int hU hs hF⟩, HasCompactSupport.intro hS fun x hx => ?_⟩, fun _ => rfl,
    fun v => ?_⟩
  · exact integral_eq_zero_of_ae (hs.mono fun k hk => h0 x hx k hk)
  · rw [UnitaryRep.integrated_ccToL1_apply]
    change ∫ x, (∫ k, F x k ∂ν) • π x v ∂μ = _
    simp only [← integral_smul_const]
    refine integral_integral_swap (integrable_ae_cpt (hS.prod hU)
      (hF.smul ((π.continuous_orbit v).comp continuous_fst)) ?_)
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs] with q h2 h
    have : F q.1 q.2 = 0 := h0 _ (fun h1 => h ⟨h1, h2⟩) _ h2
    change F q.1 q.2 • π q.1 v = 0
    rw [this, zero_smul]

/- English proof (translation)
Establish `ha` using `a.continuous`. Take `⟨f, h1, h2⟩` from `op_swap π μ hU hs (F := fun x k => e k * a (k⁻¹ * x)) (by fun_prop) (hU.mul a.hasCompactSupport.isCompact) fun x hx k hk => by`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨k, hk, k⁻¹ * x, subset_tsupport _ (mul_ne_zero_iff.1 hne).2, mul_inv_cancel_left _ _⟩`. Use `⟨f, h1, fun v => (h2 v).trans ?_⟩` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `k`. Establish `hi : Integrable (fun z => a z • π z v) μ` using `(a.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport a.hasCompactSupport.smul_right`. Rewrite using `[UnitaryRep.integrated_ccToL1_apply, ← ContinuousLinearMap.integral_comp_comm _ hi, ← integral_smul, ← integral_mul_left_eq_self _ k]`. Simplify using `only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]`.
-/
private theorem avg_left (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, e k * a (k⁻¹ * x) ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v =
        ∫ k, e k • π k (π.integrated μ (UnitaryRep.ccToL1 μ a) v) ∂ν := by
  have ha := a.continuous
  obtain ⟨f, h1, h2⟩ := op_swap π μ hU hs (F := fun x k => e k * a (k⁻¹ * x)) (by fun_prop)
    (hU.mul a.hasCompactSupport.isCompact) fun x hx k hk => by
      by_contra hne
      exact hx ⟨k, hk, k⁻¹ * x, subset_tsupport _ (mul_ne_zero_iff.1 hne).2, mul_inv_cancel_left _ _⟩
  refine ⟨f, h1, fun v => (h2 v).trans ?_⟩
  congr 1
  funext k
  have hi : Integrable (fun z => a z • π z v) μ :=
    (a.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport a.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← ContinuousLinearMap.integral_comp_comm _ hi, ← integral_smul,
    ← integral_mul_left_eq_self _ k]
  simp only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]

/- English proof (translation)
Establish `ha` using `a.continuous`. Take `⟨f, h1, h2⟩` from `op_swap π μ hU hs (F := fun x k => a (x * k⁻¹) * e k) (by fun_prop) (a.hasCompactSupport.isCompact.mul hU) fun x hx k hk => by`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨x * k⁻¹, subset_tsupport _ (mul_ne_zero_iff.1 hne).1, k, hk, inv_mul_cancel_right _ _⟩`. Use `⟨f, h1, fun v => (h2 v).trans ?_⟩` and prove the remaining obligations.

Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ (int_orbit π hU hs he v)]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[map_smul, UnitaryRep.integrated_ccToL1_apply, ← integral_smul, ← integral_mul_right_eq_self _ k]`. Simplify using `only [mul_inv_cancel_right, UnitaryRep.map_mul_apply, smul_smul, mul_comm]`.
-/
private theorem avg_right [μ.IsMulRightInvariant] (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, a (x * k⁻¹) * e k ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v =
        π.integrated μ (UnitaryRep.ccToL1 μ a) (∫ k, e k • π k v ∂ν) := by
  have ha := a.continuous
  obtain ⟨f, h1, h2⟩ := op_swap π μ hU hs (F := fun x k => a (x * k⁻¹) * e k) (by fun_prop)
    (a.hasCompactSupport.isCompact.mul hU) fun x hx k hk => by
      by_contra hne
      exact hx ⟨x * k⁻¹, subset_tsupport _ (mul_ne_zero_iff.1 hne).1, k, hk, inv_mul_cancel_right _ _⟩
  refine ⟨f, h1, fun v => (h2 v).trans ?_⟩
  rw [← ContinuousLinearMap.integral_comp_comm _ (int_orbit π hU hs he v)]
  congr 1
  funext k
  rw [map_smul, UnitaryRep.integrated_ccToL1_apply, ← integral_smul, ← integral_mul_right_eq_self _ k]
  simp only [mul_inv_cancel_right, UnitaryRep.map_mul_apply, smul_smul, mul_comm]

/- English proof (translation)
Establish `hi : Integrable e ν` using `integrable_ae_cpt hU he (hs.mono fun _ h h' => absurd h h')`. Use `⟨π.integrated ν (hi.toL1 e), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[UnitaryRep.integrated_apply]`. Conclude with `integral_congr_ae (hi.coeFn_toL1.mono fun k hk => by simp only [hk])`.
-/
private theorem proj_ex (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e) :
    ∃ E : H →L[ℂ] H, ∀ v, E v = ∫ k, e k • π k v ∂ν := by
  have hi : Integrable e ν := integrable_ae_cpt hU he (hs.mono fun _ h h' => absurd h h')
  refine ⟨π.integrated ν (hi.toL1 e), fun v => ?_⟩
  rw [UnitaryRep.integrated_apply]
  exact integral_congr_ae (hi.coeFn_toL1.mono fun k hk => by simp only [hk])

/- English proof (translation)
Take `⟨E, hE⟩` from `proj_ex π hU hs he`. Use `⟨E, fun a h => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨f, h1, h2⟩` from `avg_left π μ hU hs he a`. Take `⟨f', h1', h2'⟩` from `avg_right π μ hU hs he a`. Take `rfl : f = a` from `CompactlySupportedContinuousMap.ext fun x => (h1 x).trans (h x).1`.

Take `rfl : f' = f` from `CompactlySupportedContinuousMap.ext fun x => (h1' x).trans (h x).2`. Conclude with `⟨ContinuousLinearMap.ext fun v => (hE _).trans (h2 v).symm, ContinuousLinearMap.ext fun v => by rw [ContinuousLinearMap.comp_apply, hE, ← h2']⟩`. Take `⟨b, h1, h2⟩` from `avg_right π μ hU hs he a`. Take `⟨f, h3, h4⟩` from `avg_left π μ hU hs he b`. Establish `ha` using `a.continuous`.

Establish `hb` using `b.continuous`. Establish `hbr : ∀ g, ∫ k, b (g * k⁻¹) * e k ∂ν = b g` using `fun g => by`. Use `idem_int hU hs hi he hid (φ := fun h => a (g * h⁻¹)) (by fun_prop)` as an intermediate fact. Simplify using `only [← integral_const_mul] at this`. Rewrite `this` using `[swap_cpt hU hs (by fun_prop)]`.

Simplify using `only [h1, ← integral_mul_const]`. Use `Eq.trans ?_ (this.trans ?_)` and prove the remaining obligations. Simplify using `only [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]`. Simplify using `only [mul_comm]`. Use `⟨f, fun g => ⟨?_, ?_⟩, ContinuousLinearMap.ext fun v => ?_⟩` and prove the remaining obligations.

Use `idem_int hU hs hi he hid (φ := fun h => b (h⁻¹ * g)) (by fun_prop)` as an intermediate fact. Simplify using `only [h3]`. Simplify `this` using `only [mul_inv_rev, mul_assoc]`. Simplify using `only [h3, ← integral_mul_const]`. Rewrite using `[swap_cpt hU hs (by fun_prop)]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← hbr, ← integral_const_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[h4, h2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hE, hE]`.
-/
private theorem two_sided [μ.IsMulRightInvariant] (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) (he : Continuous e)
    (hid : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k) :
    ∃ E : H →L[ℂ] H,
      (∀ a : CompactlySupportedContinuousMap G ℂ,
        (∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g ∧ ∫ k, a (g * k⁻¹) * e k ∂ν = a g) →
        E ∘L π.integrated μ (UnitaryRep.ccToL1 μ a) = π.integrated μ (UnitaryRep.ccToL1 μ a) ∧
        π.integrated μ (UnitaryRep.ccToL1 μ a) ∘L E = π.integrated μ (UnitaryRep.ccToL1 μ a)) ∧
      ∀ a : CompactlySupportedContinuousMap G ℂ, ∃ f : CompactlySupportedContinuousMap G ℂ,
        (∀ g, ∫ k, e k * f (k⁻¹ * g) ∂ν = f g ∧ ∫ k, f (g * k⁻¹) * e k ∂ν = f g) ∧
        π.integrated μ (UnitaryRep.ccToL1 μ f) = E ∘L π.integrated μ (UnitaryRep.ccToL1 μ a) ∘L E := by
  obtain ⟨E, hE⟩ := proj_ex π hU hs he
  refine ⟨E, fun a h => ?_, fun a => ?_⟩
  · obtain ⟨f, h1, h2⟩ := avg_left π μ hU hs he a
    obtain ⟨f', h1', h2'⟩ := avg_right π μ hU hs he a
    obtain rfl : f = a := CompactlySupportedContinuousMap.ext fun x => (h1 x).trans (h x).1
    obtain rfl : f' = f := CompactlySupportedContinuousMap.ext fun x => (h1' x).trans (h x).2
    exact ⟨ContinuousLinearMap.ext fun v => (hE _).trans (h2 v).symm,
      ContinuousLinearMap.ext fun v => by rw [ContinuousLinearMap.comp_apply, hE, ← h2']⟩
  · obtain ⟨b, h1, h2⟩ := avg_right π μ hU hs he a
    obtain ⟨f, h3, h4⟩ := avg_left π μ hU hs he b
    have ha := a.continuous
    have hb := b.continuous
    have hbr : ∀ g, ∫ k, b (g * k⁻¹) * e k ∂ν = b g := fun g => by
      have := idem_int hU hs hi he hid (φ := fun h => a (g * h⁻¹)) (by fun_prop)
      simp only [← integral_const_mul] at this
      rw [swap_cpt hU hs (by fun_prop)] at this
      simp only [h1, ← integral_mul_const]
      refine Eq.trans ?_ (this.trans ?_)
      · simp only [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
      · simp only [mul_comm]
    refine ⟨f, fun g => ⟨?_, ?_⟩, ContinuousLinearMap.ext fun v => ?_⟩
    · have := idem_int hU hs hi he hid (φ := fun h => b (h⁻¹ * g)) (by fun_prop)
      simp only [h3]
      simpa only [mul_inv_rev, mul_assoc] using this
    · simp only [h3, ← integral_mul_const]
      rw [swap_cpt hU hs (by fun_prop)]
      congr 1
      funext k
      rw [← hbr, ← integral_const_mul]
      simp only [mul_assoc]
    · rw [h4, h2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hE, hE]

end General

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Amp

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

/- English proof (translation)
Establish `hs : (isExpLieAlgebra K n).IsSmoothFun fun g => β g⁻¹` using `(UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1`. Establish `hs' : (isExpLieAlgebra K n).IsSmoothFun fun g => starRingEnd ℂ (β g⁻¹)`. Use `letI := (isExpLieAlgebra K n).chartedSpace`. Conclude with `Complex.conjCLE.contDiff.comp_contMDiff hs`. Establish `hc : HasCompactSupport fun g : archGroup K n => starRingEnd ℂ (β g⁻¹)` using `(β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)`.

Use `⟨⟨⟨_, Complex.continuous_conj.comp (β.continuous.comp continuous_inv)⟩, hc⟩, hs', fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `β x = starRingEnd ℂ (starRingEnd ℂ (β x⁻¹⁻¹))`. Rewrite using `[Complex.conj_conj, inv_inv]`.
-/
private theorem star_test (β : TI K n) (hβ : SmoothT β) :
    ∃ β' : TI K n, SmoothT β' ∧ ∀ x, β x = starRingEnd ℂ (β' x⁻¹) := by
  have hs : (isExpLieAlgebra K n).IsSmoothFun fun g => β g⁻¹ :=
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1
  have hs' : (isExpLieAlgebra K n).IsSmoothFun fun g => starRingEnd ℂ (β g⁻¹) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact Complex.conjCLE.contDiff.comp_contMDiff hs
  have hc : HasCompactSupport fun g : archGroup K n => starRingEnd ℂ (β g⁻¹) :=
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  refine ⟨⟨⟨_, Complex.continuous_conj.comp (β.continuous.comp continuous_inv)⟩, hc⟩, hs', fun x => ?_⟩
  change β x = starRingEnd ℂ (starRingEnd ℂ (β x⁻¹⁻¹))
  rw [Complex.conj_conj, inv_inv]

/- English proof (translation)
The claim follows from `ContinuousLinearMap.ext fun v => UpperTheory.ConvolutionTheory.Dp.diracSep K n μ ν (T v) fun β hβ => DFunLike.congr_fun (h β hβ) v`.
-/
private theorem sep_left (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (T : LL μ →L[ℂ] LL μ)
    (h : ∀ β : TI K n, SmoothT β → Oinf μ ν β ∘L T = 0) : T = 0 :=
  ContinuousLinearMap.ext fun v => UpperTheory.ConvolutionTheory.Dp.diracSep K n μ ν (T v) fun β hβ => DFunLike.congr_fun (h β hβ) v

/- English proof (translation)
Establish `: ContinuousLinearMap.adjoint T = 0` using `sep_left ν _ fun β hβ => by`. Take `⟨β', h1, h2⟩` from `star_test β hβ`. Rewrite using `[← (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.1 β' β h2, ← ContinuousLinearMap.adjoint_comp, h β' h1, map_zero]`. Simplify using `using congrArg ContinuousLinearMap.adjoint this`.
-/
private theorem sep_right (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (T : LL μ →L[ℂ] LL μ) (h : ∀ β : TI K n, SmoothT β → T ∘L Oinf μ ν β = 0) : T = 0 := by
  have : ContinuousLinearMap.adjoint T = 0 := sep_left ν _ fun β hβ => by
    obtain ⟨β', h1, h2⟩ := star_test β hβ
    rw [← (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.1 β' β h2, ← ContinuousLinearMap.adjoint_comp, h β' h1, map_zero]
  simpa using congrArg ContinuousLinearMap.adjoint this

/- English proof (translation)
Take `⟨hc, -, -, -, -, -, -, -, hr⟩` from `UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m`. Establish `hP : ∀ γ, prj (fixF μ 𝔞.U) * Oinf μ 𝔞.ν γ = Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)` using `fun γ => ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U).2.2.2.2.2.2.2.2 _ fun u _ => hr γ u).symm.eq`. Establish `hz` using `(UpperTheory.ConvolutionTheory.Dp.capZc K n y.1).1 y.2`. Establish `h1 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀) * Oinf μ 𝔞.ν β = Oinf μ 𝔞.ν 𝔞.a₀ * Oinf μ 𝔞.ν (lact (zc y.1 y.2) β)` using `(hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ 𝔞.smooth).2.2 ‹_› hβ _ hz)).trans (hc _ _).1)`. Establish `h2 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) * Oinf μ 𝔞.ν 𝔞.a₀ = Oinf μ 𝔞.ν β * Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀)` using `(hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ hβ).2.2 ‹_› 𝔞.smooth _ hz)).trans (hc _ _).1)`.

Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `Oinf μ 𝔞.ν _ * prj _ * _ = Oinf μ 𝔞.ν _ * prj _ * _`. Rewrite using `[mul_assoc, hP, ← mul_assoc, h1, mul_assoc, ← hP, mul_assoc]`. Express the relevant statement in the definitionally equal form `_ * (Oinf μ 𝔞.ν _ * prj _) = _ * (Oinf μ 𝔞.ν _ * prj _)`. Rewrite using `[← mul_assoc, ← h2, mul_assoc]`.
-/
private theorem amp_move [IsTotallyComplex K] (𝔞 : Amp μ) (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (y : Ix K n) (β : TI K n) (hβ : SmoothT β) :
    𝔞.Z y * Oinf μ 𝔞.ν β = 𝔞.A * Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) ∧
      Oinf μ 𝔞.ν β * 𝔞.Z y = Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) * 𝔞.A := by
  obtain ⟨hc, -, -, -, -, -, -, -, hr⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m
  have hP : ∀ γ, prj (fixF μ 𝔞.U) * Oinf μ 𝔞.ν γ = Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U) := fun γ =>
    ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U).2.2.2.2.2.2.2.2 _ fun u _ => hr γ u).symm.eq
  have hz := (UpperTheory.ConvolutionTheory.Dp.capZc K n y.1).1 y.2
  have h1 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀) * Oinf μ 𝔞.ν β = Oinf μ 𝔞.ν 𝔞.a₀ * Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) :=
    (hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ 𝔞.smooth).2.2 ‹_› hβ _ hz)).trans (hc _ _).1)
  have h2 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) * Oinf μ 𝔞.ν 𝔞.a₀ = Oinf μ 𝔞.ν β * Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀) :=
    (hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ hβ).2.2 ‹_› 𝔞.smooth _ hz)).trans (hc _ _).1)
  constructor
  · change Oinf μ 𝔞.ν _ * prj _ * _ = Oinf μ 𝔞.ν _ * prj _ * _
    rw [mul_assoc, hP, ← mul_assoc, h1, mul_assoc, ← hP, mul_assoc]
  · change _ * (Oinf μ 𝔞.ν _ * prj _) = _ * (Oinf μ 𝔞.ν _ * prj _)
    rw [← mul_assoc, ← h2, mul_assoc]

/- English proof (translation)
Establish `e1 : P * 𝔞.Z y - 𝔞.Z y = 0` using `sep_right 𝔞.ν m _ fun β hβ => by`. Express the relevant statement in the definitionally equal form `(P * 𝔞.Z y - 𝔞.Z y) * _ = 0`. Rewrite using `[sub_mul, mul_assoc, (amp_move 𝔞 m y β hβ).1, ← mul_assoc, h1, sub_self]`. Establish `e2 : 𝔞.Z y * P - 𝔞.Z y = 0` using `sep_left 𝔞.ν _ fun β hβ => by`. Express the relevant statement in the definitionally equal form `_ * (𝔞.Z y * P - 𝔞.Z y) = 0`.

Rewrite using `[mul_sub, ← mul_assoc, (amp_move 𝔞 m y β hβ).2, mul_assoc, h2, sub_self]`. Rewrite using `[sub_eq_zero.1 e2, sub_eq_zero.1 e1]`.
-/
private theorem amp_fix [IsTotallyComplex K] (𝔞 : Amp μ) (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (y : Ix K n) (P : LL μ →L[ℂ] LL μ) (h1 : P * 𝔞.A = 𝔞.A) (h2 : 𝔞.A * P = 𝔞.A) :
    P * (𝔞.Z y * P) = 𝔞.Z y := by
  have e1 : P * 𝔞.Z y - 𝔞.Z y = 0 := sep_right 𝔞.ν m _ fun β hβ => by
    change (P * 𝔞.Z y - 𝔞.Z y) * _ = 0
    rw [sub_mul, mul_assoc, (amp_move 𝔞 m y β hβ).1, ← mul_assoc, h1, sub_self]
  have e2 : 𝔞.Z y * P - 𝔞.Z y = 0 := sep_left 𝔞.ν _ fun β hβ => by
    change _ * (𝔞.Z y * P - 𝔞.Z y) = 0
    rw [mul_sub, ← mul_assoc, (amp_move 𝔞 m y β hβ).2, mul_assoc, h2, sub_self]
  rw [sub_eq_zero.1 e2, sub_eq_zero.1 e1]

end Amp

/- English proof (translation)
Introduce `E _ _ _ μ _ θ 𝔢 𝔵 y`. Use `haveI := 𝔵.D.prob`. Take `⟨P, hP, hf⟩` from `two_sided (rightRegularRep (Gam E (2 + 2)) μ) μ (typeFin 𝔵.D).1 𝔵.D.supp 𝔵.D.inv 𝔵.D.cont 𝔵.D.idem`. Take `⟨m, hm, hc⟩` from `(UpperTheory.ConvolutionTheory.Tf.compatEx E (2 + 2) (by norm_num)).2.1 μ 𝔢.ν`. Take `⟨e, -, he⟩` from `UpperTheory.ConvolutionTheory.Tf.prjFix E (2 + 2) μ m 𝔢.U 𝔢.isOpen (UpperTheory.ConvolutionTheory.Tf.ampComm E (2 + 2) μ 𝔢.toAmp fun τ i => (UpperTheory.ConvolutionTheory.Dp.capZc E (2 + 2) τ).1 i).2.2.2.1`.

Establish `h0 : Rop μ (tens (lact (zc y.1 y.2) 𝔢.a₀) e) = 𝔢.toAmp.Z y` using `(UpperTheory.ConvolutionTheory.Tf.rrTens E (2 + 2) (by norm_num) μ 𝔢.ν m hc _ e).trans (by rw [he]; rfl)`. Take `⟨f, h1, h2⟩` from `hf (tens (lact (zc y.1 y.2) 𝔢.a₀) e)`. Establish `h3 : P ∘L Rop μ 𝔢.a = Rop μ 𝔢.a ∧ Rop μ 𝔢.a ∘L P = Rop μ 𝔢.a` using `hP 𝔢.a 𝔵.a_hecke`. Rewrite `h3` using `[𝔢.a_op]`. Establish `h4 : Rop μ f = P ∘L Rop μ (tens (lact (zc y.1 y.2) 𝔢.a₀) e) ∘L P` using `h2`.

Conclude with `⟨f, h1, by rw [h4, h0]; exact amp_fix 𝔢.toAmp m y P h3.1 h3.2⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genZk :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (y : Ix E (2 + 2)), ∃ f : CC E (2 + 2), 𝔵.D.Hecke f ∧ Rop μ f = 𝔢.toAmp.Z y := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 y
  haveI := 𝔵.D.prob
  obtain ⟨P, hP, hf⟩ := two_sided (rightRegularRep (Gam E (2 + 2)) μ) μ (typeFin 𝔵.D).1 𝔵.D.supp 𝔵.D.inv 𝔵.D.cont 𝔵.D.idem
  obtain ⟨m, hm, hc⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E (2 + 2) (by norm_num)).2.1 μ 𝔢.ν
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix E (2 + 2) μ m 𝔢.U 𝔢.isOpen
    (UpperTheory.ConvolutionTheory.Tf.ampComm E (2 + 2) μ 𝔢.toAmp fun τ i => (UpperTheory.ConvolutionTheory.Dp.capZc E (2 + 2) τ).1 i).2.2.2.1
  have h0 : Rop μ (tens (lact (zc y.1 y.2) 𝔢.a₀) e) = 𝔢.toAmp.Z y :=
    (UpperTheory.ConvolutionTheory.Tf.rrTens E (2 + 2) (by norm_num) μ 𝔢.ν m hc _ e).trans (by rw [he]; rfl)
  obtain ⟨f, h1, h2⟩ := hf (tens (lact (zc y.1 y.2) 𝔢.a₀) e)
  have h3 : P ∘L Rop μ 𝔢.a = Rop μ 𝔢.a ∧ Rop μ 𝔢.a ∘L P = Rop μ 𝔢.a := hP 𝔢.a 𝔵.a_hecke
  rw [𝔢.a_op] at h3
  have h4 : Rop μ f = P ∘L Rop μ (tens (lact (zc y.1 y.2) 𝔢.a₀) e) ∘L P := h2
  exact ⟨f, h1, by rw [h4, h0]; exact amp_fix 𝔢.toAmp m y P h3.1 h3.2⟩
