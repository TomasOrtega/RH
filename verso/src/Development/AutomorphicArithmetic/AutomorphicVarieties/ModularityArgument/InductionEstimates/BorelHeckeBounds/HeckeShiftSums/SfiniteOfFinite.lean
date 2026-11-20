import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.TruncKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.LamRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmBdReal
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TraceKer
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtTw
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

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
Establish `hm2 : ∀ᵐ y ∂(Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))), p y` using `(ae_map_iff (measurable_mk (Gam K n)).aemeasurable hp).2 (ae_restrict_of_ae h)`. Rewrite `hm2` using `[map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)]`. Then use the resulting hypothesis.
-/
private theorem ae_q {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {p : RightCosetSpace (Gam K n) → Prop} (hp : MeasurableSet {y | p y}) (h : ∀ᵐ x ∂μ, p (mk (Gam K n) x)) :
    ∀ᵐ y ∂quotientMeasure (Gam K n) μ, p y := by
  have hm2 : ∀ᵐ y ∂(Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))), p y :=
    (ae_map_iff (measurable_mk (Gam K n)).aemeasurable hp).2 (ae_restrict_of_ae h)
  rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)] at hm2

/- English proof (translation)
Take `⟨γ, hγ⟩` from `GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)`. Conclude with `⟨γ, γ.2, hγ.symm⟩`.
-/
private theorem out_mk {K : Type} [Field K] [NumberField K] {n : ℕ} (x : G1 K n) :
    ∃ γ ∈ Gam K n, (Quotient.out (mk (Gam K n) x) : G1 K n) = γ * x := by
  obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1
    (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
  exact ⟨γ, γ.2, hγ.symm⟩

/- English proof (translation)
Establish `a1 : ∀ x, U (P x) = P (U x)` using `fun x => DFunLike.congr_fun h1 x`. Establish `a3 : ∀ x, M (P x) = P (M x)` using `fun x => DFunLike.congr_fun h3 x`. Establish `a4 : ∀ x, Rg (P x) = P (Rg x)` using `fun x => DFunLike.congr_fun h4 x`. Establish `a5 : ∀ x, P (P x) = P x` using `fun x => DFunLike.congr_fun hPP x`. Use `⟨?_, fun φ => ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.comp_apply, a1, a3, a4, a5]`. Simplify using `only [ContinuousLinearMap.adjoint_comp, hΛ.adjoint_eq, hP.adjoint_eq, h5, ContinuousLinearMap.comp_apply]`. Rewrite using `[h2]`. Use extensionality with `x`.

Simplify using `only [ContinuousLinearMap.adjoint_comp, hΛ.adjoint_eq, hP.adjoint_eq, h5, ContinuousLinearMap.comp_apply]`.
-/
private theorem alg {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Λ P U M Ra Rg Rs : H →L[ℂ] H) (hΛ : IsSelfAdjoint Λ) (hP : IsSelfAdjoint P) (hPP : P ∘L P = P) (h1 : U ∘L P = P ∘L U)
    (h2 : U ∘L Λ = Λ ∘L U) (h3 : M ∘L P = P ∘L M) (h4 : Rg ∘L P = P ∘L Rg) (h5 : ContinuousLinearMap.adjoint Rg = Rs) :
    Λ ∘L ((Ra ∘L M ∘L Rg) ∘L U) ∘L P ∘L Λ = (Λ ∘L Ra ∘L P) ∘L M ∘L (P ∘L Rg ∘L U ∘L Λ) ∧
    (∀ φ, ContinuousLinearMap.adjoint (P ∘L Rg ∘L U ∘L Λ) φ = Λ (ContinuousLinearMap.adjoint U (Rs (P φ)))) ∧
    ContinuousLinearMap.adjoint (P ∘L Rg ∘L U ∘L Λ) = ContinuousLinearMap.adjoint U ∘L (Λ ∘L Rs ∘L P) := by
  have a1 : ∀ x, U (P x) = P (U x) := fun x => DFunLike.congr_fun h1 x
  have a3 : ∀ x, M (P x) = P (M x) := fun x => DFunLike.congr_fun h3 x
  have a4 : ∀ x, Rg (P x) = P (Rg x) := fun x => DFunLike.congr_fun h4 x
  have a5 : ∀ x, P (P x) = P x := fun x => DFunLike.congr_fun hPP x
  refine ⟨?_, fun φ => ?_, ?_⟩
  · ext x
    simp only [ContinuousLinearMap.comp_apply, a1, a3, a4, a5]
  · simp only [ContinuousLinearMap.adjoint_comp, hΛ.adjoint_eq, hP.adjoint_eq, h5, ContinuousLinearMap.comp_apply]
  · rw [h2]
    ext x
    simp only [ContinuousLinearMap.adjoint_comp, hΛ.adjoint_eq, hP.adjoint_eq, h5, ContinuousLinearMap.comp_apply]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' θ a g P hP hUP hUΛ ha hDa hg hDg N'`. Use `haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ`. Use `haveI hsf : SFinite (quotientMeasure (Gam K (2 + 2)) μ) := sfinite_of_finite _`. Use `haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩`. Use `haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) := (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap`.

Use `haveI : MeasurableSpace.CountablyGenerated (RightCosetSpace (Gam K (2 + 2))) := BorelSpace.countablyGenerated`. Use `haveI : IsSeparable (quotientMeasure (Gam K (2 + 2)) μ) := isSeparable_of_sigmaFinite _`. Use `haveI : SecondCountableTopology (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) := Lp.SecondCountableTopology`. Use `haveI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) := TopologicalSpace.SecondCountableTopology.to_separableSpace`. Establish `hDs` using `hecke_star D g hDg`.

Generalize the expression as in `hs : CuspidalProjection.ccStar g = s at hg hDs ⊢`. Take `⟨k, kγ, kO, kfar, -, kT⟩` from `truncKer K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha hDa`. Take `⟨l, lγ, lO, -, ⟨C₂, N₂, hC₂, lb⟩, lT⟩` from `truncKer K μ μ₂ τ₁ τ₂ hp D d d' A A' s P hP hg hDs`. Take `⟨C₃, c, hC₃, hθ⟩` from `qhtTw K (2 + 2) μ θ`. Take `⟨C₁, hC₁, kb⟩` from `kfar (N' + c * N₂)`.

Take `⟨C₄, N₄, hC₄, b₄⟩` from `(kvBd K (2 + 2) μ s).1 (UpperTheory.ConvolutionTheory.C.polyBdAll K (2 + 2) μ s)`. Take `⟨C₅, c₅, N₅, -, hC₅, hb⟩` from `UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd (K := K)`. Take `⟨q1, -, -⟩` from `qhtBasic K (2 + 2)`. Establish `q0 : ∀ x : G1 K (2 + 2), 0 < qht x` using `fun x => zero_lt_one.trans_le (q1 x)`. Take `⟨-, hq⟩` from `qmapPres (Gam K (2 + 2)) μ θ.e θ.mem_gam θ.pres`.

Establish `hsa : ∀ u w : L2 μ, ⟪P u, w⟫_ℂ = ⟪u, P w⟫_ℂ` using `fun u w => hP.1.isSymmetric u w`. Establish `kvγ` using `(ropAe K (2 + 2) μ s).2`. Use `⟨C₁ * (C₂ * C₃ ^ N₂), by positivity, fun f M Λ T hT hM hf hΛ => ?_⟩` and prove the remaining obligations. Take `⟨⟨B₁, hB₁⟩, km, kHS, kae⟩` from `kT T Λ hT hΛ`. Take `⟨⟨B₂, hB₂⟩, lm, lHS, lae⟩` from `lT T Λ hT hΛ`.

Take `⟨e1, e2, e3⟩` from `alg Λ P θ.U M (Rop μ a) (Rop μ g) (Rop μ s) hΛ.1 hP.1 hP.2.1 hUP (hUΛ T Λ hT hΛ) hM ((Hecke₃ K μ μ₂ τ₁ τ₂ hp D d d' A A' P hP).2 g hDg) (by rw [ropAdj, hs])`. Rewrite using `[hf, e1]`. Establish `hBHS : IsHilbertSchmidt (P ∘L Rop μ g ∘L θ.U ∘L Λ)`. Use `(lHS.comp_left (ContinuousLinearMap.adjoint θ.U)).adjoint` as an intermediate fact. Rewrite `this` using `[← e3, ContinuousLinearMap.adjoint_adjoint]`. Then use the resulting hypothesis.

Take `⟨oγ, -, om⟩` from `omMeas (K := K) T`. Establish `lout : ∀ x, l T (Quotient.out (mk (Gam K (2 + 2)) x)) = l T x` using `fun x => by`. Take `⟨γ, hγ, e⟩` from `out_mk x`. Rewrite using `[e, lγ T γ hγ]`. Establish `kvout : ∀ x, UpperTheory.ConvolutionTheory.K.kv μ s (Quotient.out (mk (Gam K (2 + 2)) x)) = UpperTheory.ConvolutionTheory.K.kv μ s x` using `fun x => by`.

Take `⟨γ, hγ, e⟩` from `out_mk x`. Rewrite using `[e, kvγ γ hγ]`. Set `k₂ : RightCosetSpace (Gam K (2 + 2)) → L2 μ` to `fun y => if Om T (Quotient.out y : G1 K (2 + 2)) then P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y))) else l T (θ.e (Quotient.out y))`. Establish `m1 : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y)))`. Use `Continuous.stronglyMeasurable ?_` and prove the remaining obligations.

Rewrite using `[(isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.continuous_iff]`. Establish `: ((fun y : RightCosetSpace (Gam K (2 + 2)) => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y)))) ∘ mk (Gam K (2 + 2))) = fun x => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e x))`. Use function extensionality and compare the values at `x`. Take `⟨γ, hγ, e⟩` from `out_mk x`. Simplify using `only [Function.comp_apply, e, map_mul]`.

Rewrite using `[kvγ _ ((θ.mem_gam γ).2 hγ)]`. Rewrite using `[this]`. Conclude with `P.continuous.comp ((kvCont K (2 + 2) μ s).comp θ.e.continuous)`. Establish `m2 : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => l T (θ.e (Quotient.out y))`. Use `lm.comp_measurable hq.measurable` as an intermediate fact.

Simplify `this` using `only [Function.comp_def, lout]`. Establish `k₂m : StronglyMeasurable k₂` using `StronglyMeasurable.ite om m1 m2`. Establish `k₂b : ∀ y, ‖k₂ y‖ ≤ max (‖P‖ * (C₄ * (C₃ * (C₅ * Real.exp (N₅ * T)) ^ c) ^ N₄)) B₂` using `fun y => by`. Distinguish the cases in `hy : Om T (Quotient.out y : G1 K (2 + 2))`. Simplify using `only [k₂, if_pos hy]`.

Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Use `(P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((b₄ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 _).le ((hθ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 _).le ((hb T _ hT).1 hy) _) hC₃)) _) hC₄)) (norm_nonneg _))` and prove the remaining obligations. Simplify using `only [k₂, if_neg hy]`. Conclude with `(hB₂ _).trans (le_max_right _ _)`. Establish `bae : ∀ φ, (ContinuousLinearMap.adjoint (P ∘L Rop μ g ∘L θ.U ∘L Λ) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ) =ᵐ[quotientMeasure (Gam K (2 + 2)) μ] fun y => ⟪k₂ y, φ⟫_ℂ` using `fun φ => by`.

Establish `t1` using `twAdj K (2 + 2) μ θ ((Λ ∘L Rop μ s ∘L P) φ)`. Establish `t2` using `hq.quasiMeasurePreserving.ae (lae φ)`. Establish `t3` using `twAdj K (2 + 2) μ θ (Rop μ s (P φ))`. Establish `t4` using `hq.quasiMeasurePreserving.ae ((ropAe K (2 + 2) μ s).1 (P φ))`. Establish `t5 : ∀ w : L2 μ, ∀ᵐ y ∂quotientMeasure (Gam K (2 + 2)) μ, Om T (Quotient.out y : G1 K (2 + 2)) → (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) y = (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) y` using `fun w => by`.

Use `ae_q μ (MeasurableSet.imp om (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable)) ?_` and prove the remaining obligations. Use `filter_upwards [(lamRep K μ μ₂ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ).2.1 w] with x hx h`. Take `⟨γ, hγ, e⟩` from `out_mk x`. Rewrite `h` using `[e, oγ γ hγ]`. Conclude with `hx h`.

Use `filter_upwards [t1, t2, t3, t4, t5 (ContinuousLinearMap.adjoint θ.U (Rop μ s (P φ)))] with y u1 u2 u3 u4 u5`. Distinguish the cases in `hy : Om T (Quotient.out y : G1 K (2 + 2))`. Simplify using `only [k₂, if_pos hy]`. Rewrite using `[e2, u5 hy, u3, u4, kvout, hsa]`. Simplify using `only [k₂, if_neg hy]`.

Rewrite using `[e3, ContinuousLinearMap.comp_apply, u1, u2, lout]`. Use `⟨isTraceClass_comp kHS (hBHS.comp_left M), fun y => ⟪k T (Quotient.out y), M (k₂ y)⟫_ℂ, ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `Integrable.of_bound (km.inner (M.continuous.comp_stronglyMeasurable k₂m)).aestronglyMeasurable (B₁ * (‖M‖ * max (‖P‖ * (C₄ * (C₃ * (C₅ * Real.exp (N₅ * T)) ^ c) ^ N₄)) B₂)) (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `(norm_inner_le_norm _ _).trans (mul_le_mul (hB₁ _) ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (k₂b y) (norm_nonneg _))) (norm_nonneg _) ((norm_nonneg _).trans (hB₁ 1)))`. Conclude with `traceKer _ _ M _ _ k₂ (MemLp.of_bound km.aestronglyMeasurable _ (Filter.Eventually.of_forall fun y => hB₁ _)) (MemLp.of_bound k₂m.aestronglyMeasurable _ (Filter.Eventually.of_forall k₂b)) kHS hBHS kae bae`.

Simplify using `only [k₂, if_pos hy, kO T _ hy]`. Simplify using `only [k₂, if_neg hy]`. Establish `z0` using `q0 (Quotient.out y)`. Establish `z1` using `kb T _ hT hy`. Establish `z2 : ‖l T (θ.e (Quotient.out y))‖ ≤ C₂ * (C₃ * qht (Quotient.out y : G1 K (2 + 2)) ^ c) ^ N₂` using `(lb T _ hT).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 _).le (hθ _) _) hC₂)`.

Use `(norm_inner_le_norm _ _).trans ((mul_le_mul z1 ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left z2 (norm_nonneg _))) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[mul_pow, pow_add, pow_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famTr :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (θ : Twist μ) (a g : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → θ.U ∘L P = P ∘L θ.U →
      (∀ (T : ℝ) (Λ : L2 μ →L[ℂ] L2 μ), 0 ≤ T → IsTrunc A.J A'.J T Λ → θ.U ∘L Λ = Λ ∘L θ.U) →
      IsLeftSmooth a → D.Hecke a → IsLeftSmooth (CuspidalProjection.ccStar g) → D.Hecke g → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : CC K (2 + 2)) (M Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), 0 ≤ T → M ∘L P = P ∘L M → Rop μ f = Rop μ a ∘L M ∘L Rop μ g → IsTrunc A.J A'.J T Λ →
        IsTraceClass (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ) ∧ ∃ w : RightCosetSpace (Gam K (2 + 2)) → ℂ, Integrable w (quotientMeasure (Gam K (2 + 2)) μ) ∧
          trace (Λ ∘L (Rop μ f ∘L θ.U) ∘L P ∘L Λ) = ∫ y, w y ∂quotientMeasure (Gam K (2 + 2)) μ ∧
          (∀ y, Om T (Quotient.out y) → w y = ⟪P (kv μ a (Quotient.out y)), M (P (kv μ (CuspidalProjection.ccStar g) (θ.e (Quotient.out y))))⟫_ℂ) ∧
          ∀ y, ¬ Om T (Quotient.out y) → ‖w y‖ ≤ C * (qht (Quotient.out y : G1 K (2 + 2)) ^ N')⁻¹ * ‖M‖ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' θ a g P hP hUP hUΛ ha hDa hg hDg N'
  classical
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := 2 + 2) μ
  haveI hsf : SFinite (quotientMeasure (Gam K (2 + 2)) μ) := sfinite_of_finite _
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  haveI : MeasurableSpace.CountablyGenerated (RightCosetSpace (Gam K (2 + 2))) := BorelSpace.countablyGenerated
  haveI : IsSeparable (quotientMeasure (Gam K (2 + 2)) μ) := isSeparable_of_sigmaFinite _
  haveI : SecondCountableTopology (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) := Lp.SecondCountableTopology
  haveI : TopologicalSpace.SeparableSpace (Lp ℂ 2 (quotientMeasure (Gam K (2 + 2)) μ)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  have hDs := hecke_star D g hDg
  generalize hs : CuspidalProjection.ccStar g = s at hg hDs ⊢
  obtain ⟨k, kγ, kO, kfar, -, kT⟩ := truncKer K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha hDa
  obtain ⟨l, lγ, lO, -, ⟨C₂, N₂, hC₂, lb⟩, lT⟩ := truncKer K μ μ₂ τ₁ τ₂ hp D d d' A A' s P hP hg hDs
  obtain ⟨C₃, c, hC₃, hθ⟩ := qhtTw K (2 + 2) μ θ
  obtain ⟨C₁, hC₁, kb⟩ := kfar (N' + c * N₂)
  obtain ⟨C₄, N₄, hC₄, b₄⟩ := (kvBd K (2 + 2) μ s).1 (UpperTheory.ConvolutionTheory.C.polyBdAll K (2 + 2) μ s)
  obtain ⟨C₅, c₅, N₅, -, hC₅, hb⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd (K := K)
  obtain ⟨q1, -, -⟩ := qhtBasic K (2 + 2)
  have q0 : ∀ x : G1 K (2 + 2), 0 < qht x := fun x => zero_lt_one.trans_le (q1 x)
  obtain ⟨-, hq⟩ := qmapPres (Gam K (2 + 2)) μ θ.e θ.mem_gam θ.pres
  have hsa : ∀ u w : L2 μ, ⟪P u, w⟫_ℂ = ⟪u, P w⟫_ℂ := fun u w => hP.1.isSymmetric u w
  have kvγ := (ropAe K (2 + 2) μ s).2
  refine ⟨C₁ * (C₂ * C₃ ^ N₂), by positivity, fun f M Λ T hT hM hf hΛ => ?_⟩
  obtain ⟨⟨B₁, hB₁⟩, km, kHS, kae⟩ := kT T Λ hT hΛ
  obtain ⟨⟨B₂, hB₂⟩, lm, lHS, lae⟩ := lT T Λ hT hΛ
  obtain ⟨e1, e2, e3⟩ := alg Λ P θ.U M (Rop μ a) (Rop μ g) (Rop μ s) hΛ.1 hP.1 hP.2.1 hUP (hUΛ T Λ hT hΛ) hM
    ((Hecke₃ K μ μ₂ τ₁ τ₂ hp D d d' A A' P hP).2 g hDg) (by rw [ropAdj, hs])
  rw [hf, e1]
  have hBHS : IsHilbertSchmidt (P ∘L Rop μ g ∘L θ.U ∘L Λ) := by
    have := (lHS.comp_left (ContinuousLinearMap.adjoint θ.U)).adjoint
    rwa [← e3, ContinuousLinearMap.adjoint_adjoint] at this
  obtain ⟨oγ, -, om⟩ := omMeas (K := K) T
  have lout : ∀ x, l T (Quotient.out (mk (Gam K (2 + 2)) x)) = l T x := fun x => by
    obtain ⟨γ, hγ, e⟩ := out_mk x
    rw [e, lγ T γ hγ]
  have kvout : ∀ x, UpperTheory.ConvolutionTheory.K.kv μ s (Quotient.out (mk (Gam K (2 + 2)) x)) = UpperTheory.ConvolutionTheory.K.kv μ s x := fun x => by
    obtain ⟨γ, hγ, e⟩ := out_mk x
    rw [e, kvγ γ hγ]
  let k₂ : RightCosetSpace (Gam K (2 + 2)) → L2 μ := fun y =>
    if Om T (Quotient.out y : G1 K (2 + 2)) then P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y))) else l T (θ.e (Quotient.out y))
  have m1 : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y))) := by
    refine Continuous.stronglyMeasurable ?_
    rw [(isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.continuous_iff]
    have : ((fun y : RightCosetSpace (Gam K (2 + 2)) => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e (Quotient.out y)))) ∘ mk (Gam K (2 + 2))) =
        fun x => P (UpperTheory.ConvolutionTheory.K.kv μ s (θ.e x)) := by
      funext x
      obtain ⟨γ, hγ, e⟩ := out_mk x
      simp only [Function.comp_apply, e, map_mul]
      rw [kvγ _ ((θ.mem_gam γ).2 hγ)]
    rw [this]
    exact P.continuous.comp ((kvCont K (2 + 2) μ s).comp θ.e.continuous)
  have m2 : StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => l T (θ.e (Quotient.out y)) := by
    have := lm.comp_measurable hq.measurable
    simpa only [Function.comp_def, lout] using this
  have k₂m : StronglyMeasurable k₂ := StronglyMeasurable.ite om m1 m2
  have k₂b : ∀ y, ‖k₂ y‖ ≤ max (‖P‖ * (C₄ * (C₃ * (C₅ * Real.exp (N₅ * T)) ^ c) ^ N₄)) B₂ := fun y => by
    by_cases hy : Om T (Quotient.out y : G1 K (2 + 2))
    · simp only [k₂, if_pos hy]
      refine le_trans ?_ (le_max_left _ _)
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((b₄ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (q0 _).le ((hθ _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (q0 _).le ((hb T _ hT).1 hy) _) hC₃)) _) hC₄)) (norm_nonneg _))
    · simp only [k₂, if_neg hy]
      exact (hB₂ _).trans (le_max_right _ _)
  have bae : ∀ φ, (ContinuousLinearMap.adjoint (P ∘L Rop μ g ∘L θ.U ∘L Λ) φ : RightCosetSpace (Gam K (2 + 2)) → ℂ)
      =ᵐ[quotientMeasure (Gam K (2 + 2)) μ] fun y => ⟪k₂ y, φ⟫_ℂ := fun φ => by
    have t1 := twAdj K (2 + 2) μ θ ((Λ ∘L Rop μ s ∘L P) φ)
    have t2 := hq.quasiMeasurePreserving.ae (lae φ)
    have t3 := twAdj K (2 + 2) μ θ (Rop μ s (P φ))
    have t4 := hq.quasiMeasurePreserving.ae ((ropAe K (2 + 2) μ s).1 (P φ))
    have t5 : ∀ w : L2 μ, ∀ᵐ y ∂quotientMeasure (Gam K (2 + 2)) μ, Om T (Quotient.out y : G1 K (2 + 2)) →
        (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) y = (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) y := fun w => by
      refine ae_q μ (MeasurableSet.imp om (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
        (Lp.stronglyMeasurable _).measurable)) ?_
      filter_upwards [(lamRep K μ μ₂ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ).2.1 w] with x hx h
      obtain ⟨γ, hγ, e⟩ := out_mk x
      rw [e, oγ γ hγ] at h
      exact hx h
    filter_upwards [t1, t2, t3, t4, t5 (ContinuousLinearMap.adjoint θ.U (Rop μ s (P φ)))] with y u1 u2 u3 u4 u5
    by_cases hy : Om T (Quotient.out y : G1 K (2 + 2))
    · simp only [k₂, if_pos hy]
      rw [e2, u5 hy, u3, u4, kvout, hsa]
    · simp only [k₂, if_neg hy]
      rw [e3, ContinuousLinearMap.comp_apply, u1, u2, lout]
  refine ⟨isTraceClass_comp kHS (hBHS.comp_left M), fun y => ⟪k T (Quotient.out y), M (k₂ y)⟫_ℂ, ?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · refine Integrable.of_bound (km.inner (M.continuous.comp_stronglyMeasurable k₂m)).aestronglyMeasurable
      (B₁ * (‖M‖ * max (‖P‖ * (C₄ * (C₃ * (C₅ * Real.exp (N₅ * T)) ^ c) ^ N₄)) B₂)) (Filter.Eventually.of_forall fun y => ?_)
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (hB₁ _) ((M.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (k₂b y) (norm_nonneg _))) (norm_nonneg _) ((norm_nonneg _).trans (hB₁ 1)))
  · exact traceKer _ _ M _ _ k₂ (MemLp.of_bound km.aestronglyMeasurable _ (Filter.Eventually.of_forall fun y => hB₁ _))
      (MemLp.of_bound k₂m.aestronglyMeasurable _ (Filter.Eventually.of_forall k₂b)) kHS hBHS kae bae
  · simp only [k₂, if_pos hy, kO T _ hy]
  · simp only [k₂, if_neg hy]
    have z0 := q0 (Quotient.out y)
    have z1 := kb T _ hT hy
    have z2 : ‖l T (θ.e (Quotient.out y))‖ ≤ C₂ * (C₃ * qht (Quotient.out y : G1 K (2 + 2)) ^ c) ^ N₂ :=
      (lb T _ hT).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (q0 _).le (hθ _) _) hC₂)
    refine (norm_inner_le_norm _ _).trans ((mul_le_mul z1 ((M.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left z2 (norm_nonneg _))) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_))
    rw [mul_pow, pow_add, pow_mul]
    field_simp
