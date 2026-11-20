import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Unfold `trace`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use extensionality with `i`. Rewrite using `[ContinuousLinearMap.smul_apply, inner_smul_right]`.
-/
private theorem trace_smul' (c : ℂ) (T : H →L[ℂ] H) : trace (c • T) = c * trace T := by
  unfold trace
  rw [← tsum_mul_left]
  congr 1
  ext i
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]

/- English proof (translation)
Use `⟨fun v => ?_, fun v hv => ?_, fun v w => ?_⟩` and prove the remaining obligations. Establish `h1 : prj V v ∈ V.topologicalClosure` using `V.topologicalClosure.starProjection_apply_mem v`. Rewrite `h1` using `[hV.submodule_topologicalClosure_eq]`. Then use the resulting hypothesis. Conclude with `Submodule.starProjection_eq_self_iff.2 (V.le_topologicalClosure hv)`. Conclude with `Submodule.inner_starProjection_left_eq_right _ v w`.
-/
private theorem prj_of_closed (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ ∀ v w, inner ℂ (prj V v) w = inner ℂ v (prj V w) := by
  refine ⟨fun v => ?_, fun v hv => ?_, fun v w => ?_⟩
  · have h1 : prj V v ∈ V.topologicalClosure := V.topologicalClosure.starProjection_apply_mem v
    rwa [hV.submodule_topologicalClosure_eq] at h1
  · exact Submodule.starProjection_eq_self_iff.2 (V.le_topologicalClosure hv)
  · exact Submodule.inner_starProjection_left_eq_right _ v w

/- English proof (translation)
Introduce `v hv`. Take `⟨h1, h2, -⟩` from `prj_of_closed V hV`. Use `congrArg (fun S : H →L[ℂ] H => S v) h` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, h2 v hv] at this`. Rewrite using `[this]`.

Conclude with `h1 _`.
-/
private theorem mem_of_comm (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (h : T ∘L prj V = prj V ∘L T) : ∀ v ∈ V, T v ∈ V := by
  intro v hv
  obtain ⟨h1, h2, -⟩ := prj_of_closed V hV
  have := congrArg (fun S : H →L[ℂ] H => S v) h
  simp only [ContinuousLinearMap.comp_apply, h2 v hv] at this
  rw [this]
  exact h1 _

/- English proof (translation)
Establish `hE : IsClosed ((eigIn V A x : Submodule ℂ H) : Set H)` using `Submodule.closed_of_finiteDimensional _`. Take `⟨e1, e2, e3⟩` from `prj_of_closed _ hE`. Take `⟨f1, f2, f3⟩` from `prj_of_closed _ hV`. Establish `hAa : ContinuousLinearMap.adjoint A = A` using `adjoint_eq_of_nonneg hA`. Establish `hAs : ∀ v w, inner ℂ (A v) w = inner ℂ v (A w)` using `fun v w => by`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_right, hAa]`. Establish `hmem : ∀ v, v ∈ eigIn V A x ↔ v ∈ V ∧ A v = (x : ℂ) • v` using `fun v => by`. Unfold `eigIn`. Rewrite using `[Submodule.mem_inf, Module.End.mem_eigenspace_iff]`. Both sides reduce to the same expression.

Establish `hadj : ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint Q v ∈ eigIn V A x`. Introduce `v hv`. Take `⟨hv1, hv2⟩` from `(hmem v).1 hv`. Use `(hmem _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: prj V (ContinuousLinearMap.adjoint Q v) = ContinuousLinearMap.adjoint Q v`.

Use `ext_inner_right ℂ fun w => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun S : H →L[ℂ] H => S w) hQV`. Simplify using `only [ContinuousLinearMap.comp_apply] at h`. Rewrite using `[f3, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, h, ← f3, f2 v hv1]`. Rewrite using `[← this]`.

Conclude with `f1 _`. Use `ext_inner_right ℂ fun w => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun S : H →L[ℂ] H => S w) hQA`. Simplify using `only [ContinuousLinearMap.comp_apply] at h`. Rewrite using `[hAs, ContinuousLinearMap.adjoint_inner_left, h, ← hAs, hv2, inner_smul_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left]`.

Establish `key : ∀ w, prj (eigIn V A x) (A (Q w)) = ((x : ℂ) * a) • prj (eigIn V A x) w`. Introduce `w`. Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Establish `hu` using `e1 u`. Rewrite using `[← e3, ← hAs, ((hmem _).1 hu).2, inner_smul_left, ← ContinuousLinearMap.adjoint_inner_left, ← e2 _ (hadj _ hu), e3, ContinuousLinearMap.adjoint_inner_left, ha _ (e1 w), inner_smul_right, inner_smul_right, e3, e2 _ (e1 w), Complex.conj_ofReal, mul_assoc]`.

Unfold `trOn`. Rewrite using `[← trace_smul']`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, key]`.
-/
private theorem trOn_eig (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A Q B : H →L[ℂ] H) (hA : 0 ≤ A) (x : ℝ) (a : ℂ)
    [FiniteDimensional ℂ (eigIn V A x)] (hQV : Q ∘L prj V = prj V ∘L Q) (hQA : Q ∘L A = A ∘L Q)
    (ha : ∀ v ∈ eigIn V A x, Q v = a • v) :
    trOn (eigIn V A x) (A ∘L Q ∘L B) = x * a * trOn (eigIn V A x) B := by
  have hE : IsClosed ((eigIn V A x : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  obtain ⟨e1, e2, e3⟩ := prj_of_closed _ hE
  obtain ⟨f1, f2, f3⟩ := prj_of_closed _ hV
  have hAa : ContinuousLinearMap.adjoint A = A := adjoint_eq_of_nonneg hA
  have hAs : ∀ v w, inner ℂ (A v) w = inner ℂ v (A w) := fun v w => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hAa]
  have hmem : ∀ v, v ∈ eigIn V A x ↔ v ∈ V ∧ A v = (x : ℂ) • v := fun v => by
    unfold eigIn
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    rfl
  have hadj : ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint Q v ∈ eigIn V A x := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := (hmem v).1 hv
    refine (hmem _).2 ⟨?_, ?_⟩
    · have : prj V (ContinuousLinearMap.adjoint Q v) = ContinuousLinearMap.adjoint Q v := by
        refine ext_inner_right ℂ fun w => ?_
        have h := congrArg (fun S : H →L[ℂ] H => S w) hQV
        simp only [ContinuousLinearMap.comp_apply] at h
        rw [f3, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, h, ← f3, f2 v hv1]
      rw [← this]
      exact f1 _
    · refine ext_inner_right ℂ fun w => ?_
      have h := congrArg (fun S : H →L[ℂ] H => S w) hQA
      simp only [ContinuousLinearMap.comp_apply] at h
      rw [hAs, ContinuousLinearMap.adjoint_inner_left, h, ← hAs, hv2, inner_smul_left, inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left]
  have key : ∀ w, prj (eigIn V A x) (A (Q w)) = ((x : ℂ) * a) • prj (eigIn V A x) w := by
    intro w
    refine ext_inner_left ℂ fun u => ?_
    have hu := e1 u
    rw [← e3, ← hAs, ((hmem _).1 hu).2, inner_smul_left, ← ContinuousLinearMap.adjoint_inner_left,
      ← e2 _ (hadj _ hu), e3, ContinuousLinearMap.adjoint_inner_left, ha _ (e1 w), inner_smul_right,
      inner_smul_right, e3, e2 _ (e1 w), Complex.conj_ofReal, mul_assoc]
  unfold trOn
  rw [← trace_smul']
  congr 1
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, key]

/- English proof (translation)
Establish `h1 : ∀ (y : MvPolynomial (Option σ) ℂ) (p : Polynomial ℂ), ψ (Polynomial.aeval y p) = Polynomial.aeval (ψ y) p`. Introduce `y p`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `monomial k c`.

Simplify using `only [Polynomial.aeval_monomial, map_mul, map_pow, MvPolynomial.algebraMap_eq, hc, Algebra.algebraMap_eq_smul_one]`. Establish `hs : IsSelfAdjoint A` using `isSelfAdjoint_of_nonneg hA`. Establish `h2 : cheb η m = fun a => ((Polynomial.Chebyshev.T ℝ m).comp (Polynomial.C (2 / η) * Polynomial.X - 1)).eval a`. Use function extensionality and compare the values at `a`. Unfold `cheb`.

Rewrite using `[Polynomial.eval_comp]`. Use `congr 1`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`.

Unfold `fcalc`. Rewrite using `[cfc_polynomial _ A hs, Polynomial.aeval_comp, ← Polynomial.Chebyshev.map_T (algebraMap ℝ ℂ), Polynomial.aeval_map_algebraMap]`. Use `congr 2`. Simplify using `only [map_sub, map_mul, map_one, hc, hX, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]`.
-/
private theorem cheb_ev {σ : Type} (ψ : MvPolynomial (Option σ) ℂ →+* (H →L[ℂ] H)) (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (hc : ∀ c : ℂ, ψ (C c) = c • 1) (hX : ψ (X none) = A) (η : ℝ) (m : ℕ) :
    ψ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option σ) ℂ) (Polynomial.Chebyshev.T ℂ m)) =
      fcalc (cheb η m) A := by
  have h1 : ∀ (y : MvPolynomial (Option σ) ℂ) (p : Polynomial ℂ), ψ (Polynomial.aeval y p) = Polynomial.aeval (ψ y) p := by
    intro y p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial k c =>
      simp only [Polynomial.aeval_monomial, map_mul, map_pow, MvPolynomial.algebraMap_eq, hc, Algebra.algebraMap_eq_smul_one]
  have hs : IsSelfAdjoint A := isSelfAdjoint_of_nonneg hA
  have h2 : cheb η m = fun a => ((Polynomial.Chebyshev.T ℝ m).comp (Polynomial.C (2 / η) * Polynomial.X - 1)).eval a := by
    funext a
    unfold cheb
    rw [Polynomial.eval_comp]
    congr 1
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    ring
  rw [h1, h2]
  unfold fcalc
  rw [cfc_polynomial _ A hs, Polynomial.aeval_comp, ← Polynomial.Chebyshev.map_T (algebraMap ℝ ℂ),
    Polynomial.aeval_map_algebraMap]
  congr 2
  simp only [map_sub, map_mul, map_one, hc, hX, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `ContinuousLinearMap.norm_id_le`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ]`.

Conclude with `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))`.
-/
private theorem norm_pow_le'' (U : H →L[ℂ] H) (j : ℕ) : ‖U ^ j‖ ≤ ‖U‖ ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/- English proof (translation)
Establish `hM : Commute (Q * U ^ j) (P * A)` using `(hQP.mul_right hQA).mul_left ((hUP.mul_right hUA).pow_left j)`. Establish `e : P ∘L (A ∘L Q ∘L (U ^ j) ∘L G) ∘L P = (Q * U ^ j) ∘L (P ∘L (A ∘L G) ∘L P)`. Express the relevant statement in the definitionally equal form `P * ((A * (Q * (U ^ j * G))) * P) = (Q * U ^ j) * (P * ((A * G) * P))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`.

Use `⟨h.comp_left _, ?_⟩` and prove the remaining obligations. Establish `hfin : traceNorm (P ∘L (A ∘L G) ∘L P) ≠ ⊤` using `((isTraceClass_iff _).1 h).ne`. Establish `h1` using `ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hfin) (traceNorm_comp_left_le (Q * U ^ j) (P ∘L (A ∘L G) ∘L P))`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_mul, toReal_enorm, mul_comm, mul_assoc]`.

Use `mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le'' U j) (norm_nonneg _))`.
-/
private theorem tn_bound (P A G Q U : H →L[ℂ] H) (j : ℕ) (h : IsTraceClass (P ∘L (A ∘L G) ∘L P))
    (hQP : Commute Q P) (hUP : Commute U P) (hQA : Commute Q A) (hUA : Commute U A) :
    IsTraceClass (P ∘L (A ∘L Q ∘L (U ^ j) ∘L G) ∘L P) ∧
      (traceNorm (P ∘L (A ∘L Q ∘L (U ^ j) ∘L G) ∘L P)).toReal ≤
        (traceNorm (P ∘L (A ∘L G) ∘L P)).toReal * ‖U‖ ^ j * ‖Q‖ := by
  have hM : Commute (Q * U ^ j) (P * A) := (hQP.mul_right hQA).mul_left ((hUP.mul_right hUA).pow_left j)
  have e : P ∘L (A ∘L Q ∘L (U ^ j) ∘L G) ∘L P = (Q * U ^ j) ∘L (P ∘L (A ∘L G) ∘L P) := by
    change P * ((A * (Q * (U ^ j * G))) * P) = (Q * U ^ j) * (P * ((A * G) * P))
    calc _ = (P * A) * (Q * U ^ j) * (G * P) := by simp only [mul_assoc]
      _ = _ := by rw [← hM.eq]; simp only [mul_assoc]
  rw [e]
  refine ⟨h.comp_left _, ?_⟩
  have hfin : traceNorm (P ∘L (A ∘L G) ∘L P) ≠ ⊤ := ((isTraceClass_iff _).1 h).ne
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hfin)
    (traceNorm_comp_left_le (Q * U ^ j) (P ∘L (A ∘L G) ∘L P))
  refine h1.trans ?_
  rw [ENNReal.toReal_mul, toReal_enorm, mul_comm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  rw [mul_comm]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le'' U j) (norm_nonneg _))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `P * ((A * (((X * Q) * U) * G)) * (T * P)) = P * (X * ((A * (Q * (U * G))) * (T * P)))`. Rewrite using `[← mul_assoc X (A * _), ← mul_assoc X A, hc.eq]`. Simplify using `only [mul_assoc]`.
-/
private theorem reassoc (P A G Q U X T : H →L[ℂ] H) (hc : Commute X A) :
    P ∘L (A ∘L ((X * Q) ∘L U) ∘L G) ∘L T ∘L P = P ∘L X ∘L (A ∘L Q ∘L U ∘L G) ∘L T ∘L P := by
  change P * ((A * (((X * Q) * U) * G)) * (T * P)) = P * (X * ((A * (Q * (U * G))) * (T * P)))
  rw [← mul_assoc X (A * _), ← mul_assoc X A, hc.eq]
  simp only [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem reassoc' (A G Q U T : H →L[ℂ] H) : (A ∘L Q ∘L U ∘L G) ∘L T = A ∘L Q ∘L U ∘L G ∘L T := rfl

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `K _ _ _ n l hn μ _ θ 𝔰 ev hev hin`. Establish `hA : 0 ≤ 𝔰.toAmp.A` using `(evEx K n hn μ 𝔰.toAmp).1`. Establish `hPc : prj (cuspidalL2 μ) = Pc μ`. Unfold `prj Pc`. Use `congr 1`.

Conclude with `(isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq`. Establish `hinP : ∀ T : LL μ →L[ℂ] LL μ, Inner μ T → Commute T (Pc μ)` using `fun T hT => by`. Establish `h` using `hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)`. Rewrite `h` using `[hPc]`. Conclude with `h`.

Establish `hR : ∀ (f : TG K n) (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v ∈ V, Rop μ f v ∈ V` using `fun f => (opBasics K n μ f).1`. Establish `hAV : ∀ V : Submodule ℂ (LL μ), IsSummand μ V → ∀ v ∈ V, 𝔰.toAmp.A v ∈ V`. Rewrite using `[← 𝔰.a_op]`. Conclude with `hR 𝔰.a`. Establish `hcpt : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ)`.

Rewrite using `[← 𝔰.a_op, ← hPc]`. Conclude with `(opBasics K n μ 𝔰.a).2.2`. Establish `htc : IsTraceClass (Pc μ ∘L (𝔰.toAmp.A ∘L Rop μ 𝔰.g) ∘L Pc μ)`. Establish `h` using `decayTraceClass K n μ 𝔰.a 𝔰.g 1 (smoothDecay K n μ _ 𝔰.a_smooth) (smoothDecay K n μ _ 𝔰.g_smooth) rfl`. Rewrite `h` using `[𝔰.a_op]`.

Conclude with `h`. Establish `hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A` using `fun Q => by`. Rewrite using `[← hev.amp]`. Conclude with `(Commute.all _ _).map ev`. Use `⟨(traceNorm (Pc μ ∘L (𝔰.toAmp.A ∘L Rop μ 𝔰.g) ∘L Pc μ)).toReal, fun η h0 h1 => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, hfd, hb⟩` from `cuspTrBand K n μ θ (Dp.multiplicity_one_cuspidal_spectrum_normOneGL K n μ) 𝔰.toAmp.A hA hAV hcpt η h0`. Use `⟨s, hs, hfd, fun Q a ha m j f hf => ?_⟩` and prove the remaining obligations. Take `⟨hbd, -, q, -, hq⟩` from `FX.cheb_bound η m h0 h1`. Establish `hcont : Continuous (cheb η m)`. Establish `: cheb η m = fun a => q.eval a` using `funext fun a => (hq a).symm`.

Rewrite using `[this]`. Conclude with `q.continuous`. Take `⟨t1, t2⟩` from `tn_bound (Pc μ) 𝔰.toAmp.A (Rop μ 𝔰.g) (ev Q) (𝔰.Uq 0) j htc (hinP _ (hin Q)) (hinP _ (𝔰.Uq_inner 0)) (hQA Q) (𝔰.Uq_amp 0)`. Establish `hTV : ∀ V : Submodule ℂ (LL μ), IsSummand μ V → ∀ v ∈ V, (𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) v ∈ V`. Introduce `V hV v hv`.

Establish `hU : Commute (𝔰.Uq 0) (prj V)` using `𝔰.Uq_inner 0 V hV.closed hV.inv`. Conclude with `hAV V hV _ (mem_of_comm V hV.closed _ (hin Q V hV.closed hV.inv) _ (mem_of_comm V hV.closed _ (hU.pow_left j).eq _ (hR _ V hV v hv)))`. Establish `h` using `hb (cheb η m) 1 _ hcont zero_le_one hbd hTV t1`. Rewrite `h` using `[one_mul]`. Establish `hch : ev (chebP η m) = fcalc (cheb η m) 𝔰.toAmp.A` using `cheb_ev (ev.comp C) _ hA hev.const hev.amp η m`.

Establish `e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L (𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) ∘L θ.U ∘L Pc μ)`. Unfold `cuspTr`. Rewrite using `[hf, map_mul, reassoc _ _ _ _ _ _ _ (hQA (chebP η m)), hch]`. Establish `e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) = ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) ∘L θ.U)`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations.

Establish `hV` using `((hs p).1 hp).2.1`. Use `haveI := hfd p hp`. Rewrite using `[reassoc', trOn_eig p.2 hV.closed 𝔰.toAmp.A (ev Q) _ hA p.1 (a p) (hin Q _ hV.closed hV.inv) (hQA Q).eq (ha p hp)]`. Rewrite using `[e1, e2]`. Conclude with `h.trans t2`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cuspPart :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n l : ℕ), 0 < n →
      ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)),
      𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → ∃ C₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ p, p ∈ s ↔ η < p.1 ∧ IsSummand μ p.2 ∧ p.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = p.2 ∧ eigIn p.2 𝔰.toAmp.A p.1 ≠ ⊥) ∧
        (∀ p ∈ s, FiniteDimensional ℂ (eigIn p.2 𝔰.toAmp.A p.1)) ∧
        ∀ (Q : PR K n) (a : ℝ × Submodule ℂ (LL μ) → ℂ), (∀ p ∈ s, ∀ v ∈ eigIn p.2 𝔰.toAmp.A p.1, ev Q v = a p • v) →
        ∀ (m j : ℕ) (f : TG K n), Rop μ f = 𝔰.toAmp.A ∘L (ev (chebP η m * Q) ∘L (𝔰.Uq 0 ^ j)) ∘L Rop μ 𝔰.g →
          ‖cuspTr μ θ f - ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U))‖ ≤
            C₁ * ‖𝔰.Uq 0‖ ^ j * ‖ev Q‖ := by
  intro K _ _ _ n l hn μ _ θ 𝔰 ev hev hin
  have hA : 0 ≤ 𝔰.toAmp.A := (evEx K n hn μ 𝔰.toAmp).1
  have hPc : prj (cuspidalL2 μ) = Pc μ := by
    unfold prj Pc
    congr 1
    exact (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
  have hinP : ∀ T : LL μ →L[ℂ] LL μ, Inner μ T → Commute T (Pc μ) := fun T hT => by
    have h := hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
    rw [hPc] at h
    exact h
  have hR : ∀ (f : TG K n) (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v ∈ V, Rop μ f v ∈ V :=
    fun f => (opBasics K n μ f).1
  have hAV : ∀ V : Submodule ℂ (LL μ), IsSummand μ V → ∀ v ∈ V, 𝔰.toAmp.A v ∈ V := by
    rw [← 𝔰.a_op]; exact hR 𝔰.a
  have hcpt : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ) := by
    rw [← 𝔰.a_op, ← hPc]; exact (opBasics K n μ 𝔰.a).2.2
  have htc : IsTraceClass (Pc μ ∘L (𝔰.toAmp.A ∘L Rop μ 𝔰.g) ∘L Pc μ) := by
    have h := decayTraceClass K n μ 𝔰.a 𝔰.g 1 (smoothDecay K n μ _ 𝔰.a_smooth) (smoothDecay K n μ _ 𝔰.g_smooth) rfl
    rw [𝔰.a_op] at h
    exact h
  have hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A := fun Q => by
    rw [← hev.amp]; exact (Commute.all _ _).map ev
  refine ⟨(traceNorm (Pc μ ∘L (𝔰.toAmp.A ∘L Rop μ 𝔰.g) ∘L Pc μ)).toReal, fun η h0 h1 => ?_⟩
  obtain ⟨s, hs, hfd, hb⟩ := cuspTrBand K n μ θ (Dp.multiplicity_one_cuspidal_spectrum_normOneGL K n μ) 𝔰.toAmp.A hA hAV hcpt η h0
  refine ⟨s, hs, hfd, fun Q a ha m j f hf => ?_⟩
  obtain ⟨hbd, -, q, -, hq⟩ := FX.cheb_bound η m h0 h1
  have hcont : Continuous (cheb η m) := by
    have : cheb η m = fun a => q.eval a := funext fun a => (hq a).symm
    rw [this]; exact q.continuous
  obtain ⟨t1, t2⟩ := tn_bound (Pc μ) 𝔰.toAmp.A (Rop μ 𝔰.g) (ev Q) (𝔰.Uq 0) j htc (hinP _ (hin Q)) (hinP _ (𝔰.Uq_inner 0))
    (hQA Q) (𝔰.Uq_amp 0)
  have hTV : ∀ V : Submodule ℂ (LL μ), IsSummand μ V → ∀ v ∈ V,
      (𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) v ∈ V := by
    intro V hV v hv
    have hU : Commute (𝔰.Uq 0) (prj V) := 𝔰.Uq_inner 0 V hV.closed hV.inv
    exact hAV V hV _ (mem_of_comm V hV.closed _ (hin Q V hV.closed hV.inv) _
      (mem_of_comm V hV.closed _ (hU.pow_left j).eq _ (hR _ V hV v hv)))
  have h := hb (cheb η m) 1 _ hcont zero_le_one hbd hTV t1
  rw [one_mul] at h
  have hch : ev (chebP η m) = fcalc (cheb η m) 𝔰.toAmp.A :=
    cheb_ev (ev.comp C) _ hA hev.const hev.amp η m
  have e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L
      (𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) ∘L θ.U ∘L Pc μ) := by
    unfold cuspTr
    rw [hf, map_mul, reassoc _ _ _ _ _ _ _ (hQA (chebP η m)), hch]
  have e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p * trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) =
      ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1)
        ((𝔰.toAmp.A ∘L ev Q ∘L (𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g) ∘L θ.U) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hV := ((hs p).1 hp).2.1
    haveI := hfd p hp
    rw [reassoc', trOn_eig p.2 hV.closed 𝔰.toAmp.A (ev Q) _ hA p.1 (a p) (hin Q _ hV.closed hV.inv) (hQA Q).eq (ha p hp)]
  rw [e1, e2]
  exact h.trans t2
