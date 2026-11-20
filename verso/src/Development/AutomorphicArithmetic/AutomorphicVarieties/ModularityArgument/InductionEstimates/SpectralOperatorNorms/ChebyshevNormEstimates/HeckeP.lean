import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Use `Measure.ext_of_lintegral _ fun φ hφ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hφ measurable_inv]`. Establish `h1 : ∫⁻ k, ∫⁻ h, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ h, φ h ∂ν`. Establish `: ∀ᵐ k ∂ν, ∫⁻ h, φ (k⁻¹ * h) ∂ν = ∫⁻ h, φ h ∂ν` using `hs.mono fun k hk => (hi _ (U.inv_mem hk)).lintegral_comp hφ`. Rewrite using `[lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]`.

Establish `h2 : ∫⁻ h, ∫⁻ k, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ k, φ k⁻¹ ∂ν`. Establish `: ∀ᵐ h ∂ν, ∫⁻ k, φ (k⁻¹ * h) ∂ν = ∫⁻ k, φ k⁻¹ ∂ν` using `hs.mono fun h hh => by`. Rewrite using `[← (hi _ (U.inv_mem hh)).lintegral_comp (f := fun k => φ k⁻¹) (hφ.comp measurable_inv)]`. Simplify using the standard rewrite rules. Rewrite using `[lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]`.

Rewrite using `[← h1, ← h2]`. Conclude with `(lintegral_lintegral_swap (f := fun k h => φ (k⁻¹ * h)) (hφ.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable).symm`.
-/
private theorem map_inv_self {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [IsProbabilityMeasure ν] (U : Subgroup G) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) : ν.map (fun k => k⁻¹) = ν := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ measurable_inv]
  have h1 : ∫⁻ k, ∫⁻ h, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ h, φ h ∂ν := by
    have : ∀ᵐ k ∂ν, ∫⁻ h, φ (k⁻¹ * h) ∂ν = ∫⁻ h, φ h ∂ν :=
      hs.mono fun k hk => (hi _ (U.inv_mem hk)).lintegral_comp hφ
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  have h2 : ∫⁻ h, ∫⁻ k, φ (k⁻¹ * h) ∂ν ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := by
    have : ∀ᵐ h ∂ν, ∫⁻ k, φ (k⁻¹ * h) ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := hs.mono fun h hh => by
      rw [← (hi _ (U.inv_mem hh)).lintegral_comp (f := fun k => φ k⁻¹) (hφ.comp measurable_inv)]
      simp
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  rw [← h1, ← h2]
  exact (lintegral_lintegral_swap (f := fun k h => φ (k⁻¹ * h))
    (hφ.comp (measurable_fst.inv.mul measurable_snd)).aemeasurable).symm

/- English proof (translation)
Use `haveI := D.prob`. Establish `hm` using `map_inv_self D.ν D.U D.supp D.inv`. Establish `hI : ∀ φ : G1 K n → ℂ, ∫ k, φ k⁻¹ ∂D.ν = ∫ k, φ k ∂D.ν` using `fun φ => by`. Use `integral_map_equiv (μ := D.ν) (MeasurableEquiv.inv (G1 K n)) φ` as an intermediate fact. Rewrite `this` using `[show (Measure.map (MeasurableEquiv.inv (G1 K n)) D.ν) = D.ν from hm]`.

Conclude with `this.symm`. Introduce `g`. Prove the components needed by the constructor for the conclusion. Rewrite using `[CuspidalProjection.ccStar_apply, ← (hf g⁻¹).2, ← integral_conj, ← hI]`. Use `integral_congr_ae (D.supp.mono fun k hk => ?_)` and prove the remaining obligations.

Simplify using `[D.star k hk, mul_comm]`. Rewrite using `[CuspidalProjection.ccStar_apply, ← (hf g⁻¹).1, ← integral_conj, ← hI]`. Use `integral_congr_ae (D.supp.mono fun k hk => ?_)` and prove the remaining obligations. Simplify using `[D.star k hk, mul_comm]`.
-/
private theorem hecke_star {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : CC K n)
    (hf : D.Hecke f) : D.Hecke (CuspidalProjection.ccStar f) := by
  haveI := D.prob
  have hm := map_inv_self D.ν D.U D.supp D.inv
  have hI : ∀ φ : G1 K n → ℂ, ∫ k, φ k⁻¹ ∂D.ν = ∫ k, φ k ∂D.ν := fun φ => by
    have := integral_map_equiv (μ := D.ν) (MeasurableEquiv.inv (G1 K n)) φ
    rw [show (Measure.map (MeasurableEquiv.inv (G1 K n)) D.ν) = D.ν from hm] at this
    exact this.symm
  intro g
  constructor
  · rw [CuspidalProjection.ccStar_apply, ← (hf g⁻¹).2, ← integral_conj, ← hI]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp [D.star k hk, mul_comm]
  · rw [CuspidalProjection.ccStar_apply, ← (hf g⁻¹).1, ← integral_conj, ← hI]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp [D.star k hk, mul_comm]

/- English proof (translation)
Use extensionality with `x`. Establish `h0 : P (x - P x) = 0`. Use `congrArg (fun T : H →L[ℂ] H => T x) hP.2.1` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply] at this`. Rewrite using `[map_sub, this, sub_self]`.

Establish `h1` using `(hP.2.2 _).1 h0`. Establish `h2 : P (Y (x - P x)) = 0`. Use `(hP.2.2 _).2 ⟨fun u => ?_, fun u => ?_⟩` and prove the remaining obligations. Take `⟨u', hu⟩` from `h u`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, hu, h1.1]`.

Take `⟨u', hu⟩` from `h' u`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, hu, h1.2]`. Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero]`. Simplify using `using h2`.
-/
private theorem half_P {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P Y : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (h : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J u) = J u')
    (h' : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J' u) = J' u') : P ∘L Y = P ∘L Y ∘L P := by
  ext x
  have h0 : P (x - P x) = 0 := by
    have := congrArg (fun T : H →L[ℂ] H => T x) hP.2.1
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [map_sub, this, sub_self]
  have h1 := (hP.2.2 _).1 h0
  have h2 : P (Y (x - P x)) = 0 := by
    refine (hP.2.2 _).2 ⟨fun u => ?_, fun u => ?_⟩
    · obtain ⟨u', hu⟩ := h u
      rw [← ContinuousLinearMap.adjoint_inner_left, hu, h1.1]
    · obtain ⟨u', hu⟩ := h' u
      rw [← ContinuousLinearMap.adjoint_inner_left, hu, h1.2]
  rw [map_sub, map_sub, sub_eq_zero] at h2
  simpa using h2

/- English proof (translation)
Establish `a` using `half_P J J' P Y hP h h'`. Establish `b` using `half_P J J' P (ContinuousLinearMap.adjoint Y) hP (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g) (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g')`. Establish `hs : ContinuousLinearMap.adjoint P = P` using `hP.1.adjoint_eq`. Establish `c` using `congrArg ContinuousLinearMap.adjoint b`. Simplify using `only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hs] at c`.

Conclude with `c.trans ((ContinuousLinearMap.comp_assoc _ _ _).trans a.symm)`.
-/
private theorem comm_P {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P Y : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (g : ∀ u, ∃ u', Y (J u) = J u') (g' : ∀ u, ∃ u', Y (J' u) = J' u')
    (h : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J u) = J u')
    (h' : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J' u) = J' u') : Y ∘L P = P ∘L Y := by
  have a := half_P J J' P Y hP h h'
  have b := half_P J J' P (ContinuousLinearMap.adjoint Y) hP
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g')
  have hs : ContinuousLinearMap.adjoint P = P := hP.1.adjoint_eq
  have c := congrArg ContinuousLinearMap.adjoint b
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hs] at c
  exact c.trans ((ContinuousLinearMap.comp_assoc _ _ _).trans a.symm)

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP`. Use `⟨fun Y => comm_P A.J A'.J P Y hP, fun f hf => ?_⟩` and prove the remaining obligations. Establish `k1 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A.J u) = A.J u'` using `fun f hf u => by`. Take `⟨β, hb⟩` from `convR K μ μ₂ τ₁ τ₂ hp D d d' A A' f hf`. Conclude with `⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩`.

Establish `k2 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A'.J u) = A'.J u'` using `fun f hf u => by`. Take `⟨β, hb⟩` from `convR K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A f hf`. Conclude with `⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩`. Use `comm_P A.J A'.J P _ hP (k1 f hf) (k2 f hf) ?_ ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.ConvolutionTheory.K.ropAdj]`.

Conclude with `k1 _ (hecke_star D f hf)`. Rewrite using `[UpperTheory.ConvolutionTheory.K.ropAdj]`. Conclude with `k2 _ (hecke_star D f hf)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Hecke₃ :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P →
      (∀ Y : L2 μ →L[ℂ] L2 μ, (∀ u, ∃ u', Y (A.J u) = A.J u') → (∀ u, ∃ u', Y (A'.J u) = A'.J u') →
        (∀ u, ∃ u', ContinuousLinearMap.adjoint Y (A.J u) = A.J u') → (∀ u, ∃ u', ContinuousLinearMap.adjoint Y (A'.J u) = A'.J u') → Y ∘L P = P ∘L Y) ∧
      ∀ f : CC K (2 + 2), D.Hecke f → Rop μ f ∘L P = P ∘L Rop μ f := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP
  refine ⟨fun Y => comm_P A.J A'.J P Y hP, fun f hf => ?_⟩
  have k1 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A.J u) = A.J u' := fun f hf u => by
    obtain ⟨β, hb⟩ := convR K μ μ₂ τ₁ τ₂ hp D d d' A A' f hf
    exact ⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩
  have k2 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A'.J u) = A'.J u' := fun f hf u => by
    obtain ⟨β, hb⟩ := convR K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A f hf
    exact ⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩
  refine comm_P A.J A'.J P _ hP (k1 f hf) (k2 f hf) ?_ ?_
  · rw [UpperTheory.ConvolutionTheory.K.ropAdj]; exact k1 _ (hecke_star D f hf)
  · rw [UpperTheory.ConvolutionTheory.K.ropAdj]; exact k2 _ (hecke_star D f hf)
