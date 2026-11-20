import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmissibleCuspFormsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.TypeOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section Avg

open Function Set
open scoped InnerProductSpace

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

/- English proof (translation)
Use `⟨hc, fun γ hγ => ?_, hr⟩` and prove the remaining obligations. Establish `h1 : (fun y => φ (γ * y)) =ᵐ[μ] φ` using `by filter_upwards [hr, (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hr] with y a b`. Rewrite using `[← a, ← b]`. Use `congr 1`. Conclude with `Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩`.

Conclude with `congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq μ hc).1 h1)`.
-/
private theorem rep_of {v : L2 μ} {φ : G1 K n → ℂ} (hc : Continuous φ) (hr : Reps μ v φ) : IsContRep μ v φ := by
  refine ⟨hc, fun γ hγ => ?_, hr⟩
  have h1 : (fun y => φ (γ * y)) =ᵐ[μ] φ := by
    filter_upwards [hr, (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hr] with y a b
    rw [← a, ← b]
    congr 1
    exact Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩
  exact congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq μ hc).1 h1)

/- English proof (translation)
The claim follows from `Lp.ext (h.ae_eq_quotFun.trans h'.ae_eq_quotFun.symm)`.
-/
private theorem rep_inj {v w : L2 μ} {F : G1 K n → ℂ} (h : IsContRep μ v F) (h' : IsContRep μ w F) : v = w :=
  Lp.ext (h.ae_eq_quotFun.trans h'.ae_eq_quotFun.symm)

/- English proof (translation)
Establish `h` using `hf.continuousOn.integrableOn_compact (μ := ν) hC`. Rewrite `h` using `[IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs]`. Then use the resulting hypothesis.
-/
private theorem integ_of {Y E : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [T2Space Y] [NormedAddCommGroup E] [SecondCountableTopologyEither Y E]
    {ν : Measure Y} [IsFiniteMeasure ν] {C : Set Y} (hC : IsCompact C) (hs : ∀ᵐ k ∂ν, k ∈ C)
    {f : Y → E} (hf : Continuous f) : Integrable f ν := by
  have h := hf.continuousOn.integrableOn_compact (μ := ν) hC
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

variable (μ) in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `hν : ν.restrict C = ν` using `Measure.restrict_eq_self_of_ae_mem hs`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : G1 K n → ℂ, Ψ = fun x => ∫ k, c k * F (x * j k) ∂ν` from `⟨_, rfl⟩`. Establish `hΨc : Continuous Ψ`. Establish `hJ : Continuous (uncurry fun (y : G1 K n) (k : Y) => c k * F (y * j k))` using `(hc.comp continuous_snd).mul (hF.1.comp (continuous_fst.mul (hj.comp continuous_snd)))`.

Establish `e : Ψ = fun y => ∫ k in C, c k * F (y * j k) ∂ν` using `by rw [hν, hΨ]`. Rewrite using `[e]`. Conclude with `continuous_parametric_integral_of_continuous hJ hC`. Establish `hΨinv : ∀ γ₀ ∈ Gam K n, ∀ y, Ψ (γ₀ * y) = Ψ y`. Introduce `γ₀ hγ₀ y`.

Rewrite using `[hΨ]`. Use `integral_congr_ae (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Use `show c a * F (γ₀ * y * j a) = c a * F (y * j a)`. Rewrite using `[mul_assoc, hF.2.1 γ₀ hγ₀]`. Rewrite using `[← hΨ]`.

Use `⟨hΨc, hΨinv, ?_⟩` and prove the remaining obligations. Take `⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun F hF.2.1` from `⟨_, rfl⟩`. Establish `hWQc : Continuous WQ` using `hWQ ▸ continuous_quotFun hF.2.1 hF.1`. Take `⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv` from `⟨_, rfl⟩`. Establish `hΨQ_eq : ∀ x, ΨQ x = ∫ k, c k * WQ (rightMul (Gam K n) (j k) x) ∂ν`.

Introduce `x`. Take `⟨y, rfl⟩` from `mk_surjective (Gam K n) x`. Rewrite using `[hΨQ, quotFun_mk, hΨ, hWQ]`. Simplify using `only [rightMul_mk, quotFun_mk]`. Establish `hJQ : Continuous (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) => c k * WQ (rightMul (Gam K n) (j k) x))`.

Establish `hr : Continuous fun p : Y × RightCosetSpace (Gam K n) => rightMul (Gam K n) (j p.1) p.2`. Establish `h1 : Continuous fun p : RightCosetSpace (Gam K n) × G1 K n => rightMul (Gam K n) p.2 p.1` using `continuous_rightMul_prod (Gam K n)`. Establish `h2 : Continuous fun p : Y × RightCosetSpace (Gam K n) => (p.2, j p.1)` using `continuous_snd.prodMk (hj.comp continuous_fst)`. Establish `h3` using `h1.comp h2`. Conclude with `h3`.

Establish `h4` using `(hc.comp continuous_fst).mul (hWQc.comp hr)`. Conclude with `h4`. Establish `hwQ : (w : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] WQ` using `hWQ ▸ hF.ae_eq_quotFun`. Establish `hWi : Integrable WQ (quotientMeasure (Gam K n) μ)` using `((Lp.memLp w).integrable one_le_two).congr hwQ`. Establish `hMP` using `fun k => measurePreserving_rightMul (Γ := Gam K n) μ (j k)`.

Establish `hfib : ∀ k, Integrable (fun x => c k * WQ (rightMul (Gam K n) (j k) x)) (quotientMeasure (Gam K n) μ)` using `fun k => ((hMP k).integrable_comp_of_integrable hWi).const_mul (c k)`. Establish `hnorm : ∀ k, ∫ x, ‖c k * WQ (rightMul (Gam K n) (j k) x)‖ ∂quotientMeasure (Gam K n) μ = ‖c k‖ * ∫ x, ‖WQ x‖ ∂quotientMeasure (Gam K n) μ`. Introduce `k`. Repeatedly rewrite using `[norm_mul]`. Rewrite using `[integral_const_mul]`.

Use `congr 1`. Use `conv_rhs => rw [← (hMP k).map_eq]`. Rewrite using `[integral_map (hMP k).measurable.aemeasurable hWQc.norm.aestronglyMeasurable]`. Establish `hint : Integrable (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) => c k * WQ (rightMul (Gam K n) (j k) x)) (ν.prod (quotientMeasure (Gam K n) μ))`. Rewrite using `[integrable_prod_iff hJQ.aestronglyMeasurable]`.

Use `⟨Eventually.of_forall hfib, ?_⟩` and prove the remaining obligations. Simplify using `only [uncurry_apply_pair, hnorm]`. Conclude with `integ_of hC hs (hc.norm.mul continuous_const)`. Establish `hint' : ∀ s : Set (RightCosetSpace (Gam K n)), Integrable (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) => c k * WQ (rightMul (Gam K n) (j k) x)) (ν.prod ((quotientMeasure (Gam K n) μ).restrict s))`. Introduce `s`.

Use `hint.restrict (s := univ ×ˢ s)` as an intermediate fact. Rewrite `this` using `[← Measure.prod_restrict, Measure.restrict_univ]`. Then use the resulting hypothesis. Establish `hΨQi : Integrable ΨQ (quotientMeasure (Gam K n) μ)` using `hint.integral_prod_right.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)`. Take `⟨V, hV⟩ : ∃ V : L2 μ, V = ∫ k, c k • rightRegularRep (Gam K n) μ (j k) w ∂ν` from `⟨_, rfl⟩`. Establish `hVi : Integrable (fun k => c k • rightRegularRep (Gam K n) μ (j k) w) ν` using `integ_of hC hs (hc.smul (((rightRegularRep (Gam K n) μ).continuous_orbit w).comp hj))`.

Establish `hVeq : (V : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] ΨQ`. Use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn) (fun s _ _ => hΨQi.integrableOn) fun s hs' hμs => ?_` and prove the remaining obligations. Rewrite using `[← L2.inner_indicatorConstLp_one hs' hμs.ne, hV, ← integral_inner hVi]`. Establish `hcoef : ∀ k, ⟪indicatorConstLp 2 hs' hμs.ne (1 : ℂ), c k • rightRegularRep (Gam K n) μ (j k) w⟫_ℂ = ∫ x in s, c k * WQ (rightMul (Gam K n) (j k) x) ∂quotientMeasure (Gam K n) μ`. Introduce `k`.

Rewrite using `[inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]`. Use `setIntegral_congr_ae hs' ?_` and prove the remaining obligations. Establish `h1` using `coeFn_rightRegularRep (Gam K n) μ (j k) w`. Establish `h2` using `(hMP k).quasiMeasurePreserving.ae_eq_comp hwQ`. Use `filter_upwards [h1, h2] with x hx1 hx2`.

Introduce `_`. Simplify using `only [Function.comp_apply] at hx2`. Conclude with `congrArg (c k * ·) (hx1.trans hx2)`. Repeatedly rewrite using `[hcoef]`. Use `(integral_integral_swap (hint' s)).trans ?_` and prove the remaining obligations.

Conclude with `setIntegral_congr_fun hs' fun x _ => (hΨQ_eq x).symm`. Rewrite using `[← hV]`. Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp hVeq] with y hy`. Simplify using `only [Function.comp_apply] at hy`. Use `hy.trans ?_` and prove the remaining obligations.

Rewrite using `[hΨQ, quotFun_mk]`.
-/
private theorem avg_rep {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] {C : Set Y} (hC : IsCompact C) (hs : ∀ᵐ k ∂ν, k ∈ C)
    {j : Y → G1 K n} (hj : Continuous j) {c : Y → ℂ} (hc : Continuous c) {w : L2 μ} {F : G1 K n → ℂ}
    (hF : IsContRep μ w F) :
    IsContRep μ (∫ k, c k • rightRegularRep (Gam K n) μ (j k) w ∂ν) (fun x => ∫ k, c k * F (x * j k) ∂ν) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hν : ν.restrict C = ν := Measure.restrict_eq_self_of_ae_mem hs
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G1 K n → ℂ, Ψ = fun x => ∫ k, c k * F (x * j k) ∂ν := ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have hJ : Continuous (uncurry fun (y : G1 K n) (k : Y) => c k * F (y * j k)) :=
      (hc.comp continuous_snd).mul (hF.1.comp (continuous_fst.mul (hj.comp continuous_snd)))
    have e : Ψ = fun y => ∫ k in C, c k * F (y * j k) ∂ν := by rw [hν, hΨ]
    rw [e]
    exact continuous_parametric_integral_of_continuous hJ hC
  have hΨinv : ∀ γ₀ ∈ Gam K n, ∀ y, Ψ (γ₀ * y) = Ψ y := by
    intro γ₀ hγ₀ y
    rw [hΨ]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show c a * F (γ₀ * y * j a) = c a * F (y * j a)
    rw [mul_assoc, hF.2.1 γ₀ hγ₀]
  rw [← hΨ]
  refine ⟨hΨc, hΨinv, ?_⟩
  obtain ⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun F hF.2.1 := ⟨_, rfl⟩
  have hWQc : Continuous WQ := hWQ ▸ continuous_quotFun hF.2.1 hF.1
  obtain ⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv := ⟨_, rfl⟩
  have hΨQ_eq : ∀ x, ΨQ x = ∫ k, c k * WQ (rightMul (Gam K n) (j k) x) ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
    rw [hΨQ, quotFun_mk, hΨ, hWQ]
    simp only [rightMul_mk, quotFun_mk]
  have hJQ : Continuous (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) =>
      c k * WQ (rightMul (Gam K n) (j k) x)) := by
    have hr : Continuous fun p : Y × RightCosetSpace (Gam K n) => rightMul (Gam K n) (j p.1) p.2 := by
      have h1 : Continuous fun p : RightCosetSpace (Gam K n) × G1 K n => rightMul (Gam K n) p.2 p.1 :=
        continuous_rightMul_prod (Gam K n)
      have h2 : Continuous fun p : Y × RightCosetSpace (Gam K n) => (p.2, j p.1) :=
        continuous_snd.prodMk (hj.comp continuous_fst)
      have h3 := h1.comp h2
      exact h3
    have h4 := (hc.comp continuous_fst).mul (hWQc.comp hr)
    exact h4
  have hwQ : (w : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] WQ := hWQ ▸ hF.ae_eq_quotFun
  have hWi : Integrable WQ (quotientMeasure (Gam K n) μ) := ((Lp.memLp w).integrable one_le_two).congr hwQ
  have hMP := fun k => measurePreserving_rightMul (Γ := Gam K n) μ (j k)
  have hfib : ∀ k, Integrable (fun x => c k * WQ (rightMul (Gam K n) (j k) x)) (quotientMeasure (Gam K n) μ) := fun k =>
    ((hMP k).integrable_comp_of_integrable hWi).const_mul (c k)
  have hnorm : ∀ k, ∫ x, ‖c k * WQ (rightMul (Gam K n) (j k) x)‖ ∂quotientMeasure (Gam K n) μ =
      ‖c k‖ * ∫ x, ‖WQ x‖ ∂quotientMeasure (Gam K n) μ := by
    intro k
    simp_rw [norm_mul]
    rw [integral_const_mul]
    congr 1
    conv_rhs => rw [← (hMP k).map_eq]
    rw [integral_map (hMP k).measurable.aemeasurable hWQc.norm.aestronglyMeasurable]
  have hint : Integrable (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) =>
      c k * WQ (rightMul (Gam K n) (j k) x)) (ν.prod (quotientMeasure (Gam K n) μ)) := by
    rw [integrable_prod_iff hJQ.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hfib, ?_⟩
    simp only [uncurry_apply_pair, hnorm]
    exact integ_of hC hs (hc.norm.mul continuous_const)
  have hint' : ∀ s : Set (RightCosetSpace (Gam K n)), Integrable (uncurry fun (k : Y) (x : RightCosetSpace (Gam K n)) =>
      c k * WQ (rightMul (Gam K n) (j k) x)) (ν.prod ((quotientMeasure (Gam K n) μ).restrict s)) := by
    intro s
    have := hint.restrict (s := univ ×ˢ s)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
  have hΨQi : Integrable ΨQ (quotientMeasure (Gam K n) μ) :=
    hint.integral_prod_right.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)
  obtain ⟨V, hV⟩ : ∃ V : L2 μ, V = ∫ k, c k • rightRegularRep (Gam K n) μ (j k) w ∂ν := ⟨_, rfl⟩
  have hVi : Integrable (fun k => c k • rightRegularRep (Gam K n) μ (j k) w) ν :=
    integ_of hC hs (hc.smul (((rightRegularRep (Gam K n) μ).continuous_orbit w).comp hj))
  have hVeq : (V : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ] ΨQ := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
      (fun s _ _ => hΨQi.integrableOn) fun s hs' hμs => ?_
    rw [← L2.inner_indicatorConstLp_one hs' hμs.ne, hV, ← integral_inner hVi]
    have hcoef : ∀ k, ⟪indicatorConstLp 2 hs' hμs.ne (1 : ℂ), c k • rightRegularRep (Gam K n) μ (j k) w⟫_ℂ =
        ∫ x in s, c k * WQ (rightMul (Gam K n) (j k) x) ∂quotientMeasure (Gam K n) μ := by
      intro k
      rw [inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
      refine setIntegral_congr_ae hs' ?_
      have h1 := coeFn_rightRegularRep (Gam K n) μ (j k) w
      have h2 := (hMP k).quasiMeasurePreserving.ae_eq_comp hwQ
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      simp only [Function.comp_apply] at hx2
      exact congrArg (c k * ·) (hx1.trans hx2)
    simp_rw [hcoef]
    refine (integral_integral_swap (hint' s)).trans ?_
    exact setIntegral_congr_fun hs' fun x _ => (hΨQ_eq x).symm
  rw [← hV]
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp hVeq] with y hy
  simp only [Function.comp_apply] at hy
  refine hy.trans ?_
  rw [hΨQ, quotFun_mk]

end Avg

section Proj

open Function Set
open scoped InnerProductSpace

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

/- English proof (translation)
Use `choose! r hr using h`. Use `⟨{ toFun := fun φ => r φ.1, map_add' := ?_, map_smul' := ?_ }, fun φ => hr _ φ.2⟩` and prove the remaining obligations. Introduce `a b`. Conclude with `rep_inj (hr _ (a + b).2) ((hr _ a.2).add (hr _ b.2))`. Introduce `c a`.

Conclude with `rep_inj (hr _ (c • a).2) ((hr _ a.2).smul c)`.
-/
private theorem lin_of (X : Submodule ℂ (G1 K n → ℂ)) (h : ∀ φ ∈ X, ∃ v : L2 μ, IsContRep μ v φ) :
    ∃ J : X →ₗ[ℂ] L2 μ, ∀ φ : X, IsContRep μ (J φ) φ.1 := by
  choose! r hr using h
  refine ⟨{ toFun := fun φ => r φ.1, map_add' := ?_, map_smul' := ?_ }, fun φ => hr _ φ.2⟩
  · intro a b
    exact rep_inj (hr _ (a + b).2) ((hr _ a.2).add (hr _ b.2))
  · intro c a
    exact rep_inj (hr _ (c • a).2) ((hr _ a.2).smul c)

/- English proof (translation)
Establish `hU : {g | ‖π g v - v‖ < ε} ∈ 𝓝 (1 : G)`. Establish `hc : Continuous fun g => ‖π g v - v‖` using `((π.continuous_orbit v).sub continuous_const).norm`. Establish `h1 : ‖π 1 v - v‖ < ε` using `by simpa using hε`. Conclude with `hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h1)`. Take `⟨U, hUsub, hUo, h1U⟩` from `mem_nhds_iff.1 hU`.

Take `⟨h, h1, h0, hcs, hrange⟩` from `exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl (Set.disjoint_singleton_left.2 fun h => h h1U)`. Establish `hnn : ∀ g, 0 ≤ h g` using `fun g => (hrange g).1`. Take `⟨c, hc⟩ : ∃ c : ℝ, c = ∫ g, h g ∂μ` from `⟨_, rfl⟩`. Establish `hcpos : 0 < c` using `hc ▸ h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)`. Establish `hint : Integrable (fun g => h g) μ` using `h.continuous.integrable_of_hasCompactSupport hcs`.

Set `f : CompactlySupportedContinuousMap G ℂ` to `⟨⟨fun g => ((c⁻¹ * h g : ℝ) : ℂ), by fun_prop⟩, (hcs.mul_left (f := fun _ => c⁻¹)).comp_left Complex.ofReal_zero⟩`. Establish `hfg : ∀ g, f g = ((c⁻¹ * h g : ℝ) : ℂ)` using `fun _ => rfl`. Use `⟨f, ?_⟩` and prove the remaining obligations. Establish `hint1 : Integrable (fun g => f g • π g v) μ` using `(f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right`. Establish `hint2 : Integrable (fun g => f g • v) μ` using `(f.continuous.smul continuous_const).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right`.

Establish `hcv : ∫ g, f g • v ∂μ = v`. Rewrite using `[integral_smul_const]`. Simplify using `only [hfg]`. Establish `: ∫ g, ((c⁻¹ * h g : ℝ) : ℂ) ∂μ = ((∫ g, c⁻¹ * h g ∂μ : ℝ) : ℂ)` using `integral_ofReal`. Rewrite using `[this, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']`.

Simplify using the standard rewrite rules. Establish `key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ`. Simplify using `only [smul_sub]`. Rewrite using `[integral_sub hint1 hint2, ← π.integrated_ccToL1_apply μ f v, hcv]`. Rewrite using `[key]`.

Establish `hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, (c⁻¹ * h g) * ε ∂μ`. Use `norm_integral_le_of_norm_le ((hint.const_mul _).mul_const _) (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g))]`. Distinguish the cases in `hg : g ∈ U`. Conclude with `mul_le_mul_of_nonneg_left (hUsub hg).le (mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g))`.

Rewrite using `[h0 hg]`. Simplify using the standard rewrite rules. Use `hbound.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[integral_mul_const, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne', one_mul]`.
-/
private theorem approx {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (v : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ ε := by
  have hU : {g | ‖π g v - v‖ < ε} ∈ 𝓝 (1 : G) := by
    have hc : Continuous fun g => ‖π g v - v‖ := ((π.continuous_orbit v).sub continuous_const).norm
    have h1 : ‖π 1 v - v‖ < ε := by simpa using hε
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h1)
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hU
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ g, h g ∂μ := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  have hint : Integrable (fun g => h g) μ := h.continuous.integrable_of_hasCompactSupport hcs
  let f : CompactlySupportedContinuousMap G ℂ := ⟨⟨fun g => ((c⁻¹ * h g : ℝ) : ℂ), by fun_prop⟩,
    (hcs.mul_left (f := fun _ => c⁻¹)).comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = ((c⁻¹ * h g : ℝ) : ℂ) := fun _ => rfl
  refine ⟨f, ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right
  have hcv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, ((c⁻¹ * h g : ℝ) : ℂ) ∂μ = ((∫ g, c⁻¹ * h g ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [this, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, ← π.integrated_ccToL1_apply μ f v, hcv]
  rw [key]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, (c⁻¹ * h g) * ε ∂μ := by
    refine norm_integral_le_of_norm_le ((hint.const_mul _).mul_const _) (Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g))]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hUsub hg).le (mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g))
    · rw [h0 hg]; simp
  refine hbound.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne', one_mul]

/- English proof (translation)
Establish `: CompleteSpace τ` using `hcl.completeSpace_coe`. Rewrite using `[← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← integral_inner hf]`. Simplify using `[Submodule.inner_left_of_mem_orthogonal (hτ _) hu]`.
-/
private theorem avg_mem {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {τ : Submodule ℂ (L2 μ)} (hcl : IsClosed (τ : Set (L2 μ)))
    {f : Y → L2 μ} (hf : Integrable f ν) (hτ : ∀ k, f k ∈ τ) : ∫ k, f k ∂ν ∈ τ := by
  have : CompleteSpace τ := hcl.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal τ, Submodule.mem_orthogonal]
  intro u hu
  rw [← integral_inner hf]
  simp [Submodule.inner_left_of_mem_orthogonal (hτ _) hu]

/- English proof (translation)
Establish `s1 : ∀ k ∈ U, ∫ l, e l * F (x * k * l) ∂ν = ∫ m, e (k⁻¹ * m) * F (x * m) ∂ν`. Introduce `k hk`. Establish `hm` using `hinv k hk`. Use `conv_rhs => rw [← hm.map_eq]`. Rewrite using `[integral_map hm.measurable.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]`.

Simplify using `only [inv_mul_cancel_left, mul_assoc]`. Establish `hsupp : ∀ᵐ p ∂(ν.prod ν), p ∈ (U : Set G) ×ˢ (U : Set G)` using `by filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs, Measure.quasiMeasurePreserving_snd.ae hs] with p a b`. Conclude with `⟨a, b⟩`. Establish `hint : Integrable (uncurry fun k m => e k * (e (k⁻¹ * m) * F (x * m))) (ν.prod ν)` using `integ_of (hU.prod hU) hsupp (by unfold uncurry; fun_prop)`. Combine the equalities or inequalities in the displayed calculation.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hs] with k hk`. Rewrite using `[s1 k hk, integral_const_mul]`. Use `_ = ∫ m, ∫ k, e k * (e (k⁻¹ * m) * F (x * m)) ∂ν ∂ν := integral_integral_swap hint`. Use `_ = ∫ m, e m * F (x * m) ∂ν := by`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hs] with m hm`. Simplify using `only [← mul_assoc]`. Rewrite using `[integral_mul_const, hid m hm]`.
-/
private theorem fix_gen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {U : Subgroup G} (hU : IsCompact (U : Set G)) {ν : Measure G} [IsProbabilityMeasure ν]
    (hs : ∀ᵐ k ∂ν, k ∈ U) (hinv : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) {e : G → ℂ} (he : Continuous e)
    (hid : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k) {F : G → ℂ} (hF : Continuous F) (x : G) :
    ∫ k, e k * ∫ l, e l * F (x * k * l) ∂ν ∂ν = ∫ m, e m * F (x * m) ∂ν := by
  have s1 : ∀ k ∈ U, ∫ l, e l * F (x * k * l) ∂ν = ∫ m, e (k⁻¹ * m) * F (x * m) ∂ν := by
    intro k hk
    have hm := hinv k hk
    conv_rhs => rw [← hm.map_eq]
    rw [integral_map hm.measurable.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [inv_mul_cancel_left, mul_assoc]
  have hsupp : ∀ᵐ p ∂(ν.prod ν), p ∈ (U : Set G) ×ˢ (U : Set G) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs, Measure.quasiMeasurePreserving_snd.ae hs] with p a b
    exact ⟨a, b⟩
  have hint : Integrable (uncurry fun k m => e k * (e (k⁻¹ * m) * F (x * m))) (ν.prod ν) :=
    integ_of (hU.prod hU) hsupp (by unfold uncurry; fun_prop)
  calc ∫ k, e k * ∫ l, e l * F (x * k * l) ∂ν ∂ν
      = ∫ k, ∫ m, e k * (e (k⁻¹ * m) * F (x * m)) ∂ν ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hs] with k hk
        rw [s1 k hk, integral_const_mul]
    _ = ∫ m, ∫ k, e k * (e (k⁻¹ * m) * F (x * m)) ∂ν ∂ν := integral_integral_swap hint
    _ = ∫ m, e m * F (x * m) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hs] with m hm
        simp only [← mul_assoc]
        rw [integral_mul_const, hid m hm]

set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Introduce `x`. Use `haveI := D.prob`. Conclude with `fix_gen (typeFin D).1 D.supp D.inv D.cont D.idem hF x`.
-/
private theorem fix_avg (D : TypeDat K n) {F : G1 K n → ℂ} (hF : Continuous F) :
    D.Fix fun x => ∫ k, D.e k * F (x * k) ∂D.ν := by
  intro x
  haveI := D.prob
  exact fix_gen (typeFin D).1 D.supp D.inv D.cont D.idem hF x

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Use `haveI := D.prob`. Use `haveI := he.haar.prob`. Establish `hU : IsCompact (D.U : Set (G1 K n))` using `(typeFin D).1`. Establish `hintD : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν` using `integ_of hU D.supp (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit v))`. Establish `hintA : Integrable (fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) κ` using `integ_of isCompact_univ (Eventually.of_forall fun _ => Set.mem_univ _) (he.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hac))`.

Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations. Establish `hc : Continuous fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ` using `continuous_const.inner ((rightRegularRep (Gam K n) μ).continuous_orbit v)`. Establish `hA : FixA κ e fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ`. Introduce `g`. Establish `e1` using `((innerSL ℂ u).comp (rightRegularRep (Gam K n) μ g)).integral_comp_comm hintA`.

Establish `e2 : ∫ k, e k • rightRegularRep (Gam K n) μ (arc1 k) v ∂κ = v` using `hp`. Rewrite `e1` using `[e2]`. Use `Eq.trans (integral_congr_ae (Eventually.of_forall fun k => ?_)) e1` and prove the remaining obligations. Simplify using `[UnitaryRep.map_mul_apply, inner_smul_right]`. Establish `hFx : FixF U₀ fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ`.

Introduce `y hy g`. Establish `h1 : rightRegularRep (Gam K n) μ (fin1 y) v = v`. Use `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv y) hy` as an intermediate fact. Conclude with `this`. Establish `h2 : rightRegularRep (Gam K n) μ (g * fin1 y) v = rightRegularRep (Gam K n) μ g (rightRegularRep (Gam K n) μ (fin1 y) v)` using `UnitaryRep.map_mul_apply _ g (fin1 y) v`.

Conclude with `congrArg (fun z => ⟪u, z⟫_ℂ) (h2.trans (congrArg _ h1))`. Establish `hfix` using `(hT.fix _ hc).2 ⟨hA, hFx⟩ 1`. Rewrite using `[← integral_inner hintD]`. Simplify using `only [inner_smul_right]`. Simplify using `using hfix`.
-/
private theorem fixed_of (D : TypeDat K n) {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} {U₀ : Subgroup (FA K n)}
    (hT : IsTy D κ e U₀) (he : IdemA κ e) (hac : Continuous (arc1 : archCompact K n → G1 K n)) (hcomp : CompactSpace (archCompact K n))
    {v : L2 μ} (hp : pOp μ κ e v = v) (hv : v ∈ fixF μ U₀) :
    ∫ k, D.e k • rightRegularRep (Gam K n) μ k v ∂D.ν = v := by
  haveI := D.prob
  haveI := he.haar.prob
  have hU : IsCompact (D.U : Set (G1 K n)) := (typeFin D).1
  have hintD : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k v) D.ν :=
    integ_of hU D.supp (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit v))
  have hintA : Integrable (fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) κ :=
    integ_of isCompact_univ (Eventually.of_forall fun _ => Set.mem_univ _)
      (he.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hac))
  refine ext_inner_left ℂ fun u => ?_
  have hc : Continuous fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ :=
    continuous_const.inner ((rightRegularRep (Gam K n) μ).continuous_orbit v)
  have hA : FixA κ e fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ := by
    intro g
    have e1 := ((innerSL ℂ u).comp (rightRegularRep (Gam K n) μ g)).integral_comp_comm hintA
    have e2 : ∫ k, e k • rightRegularRep (Gam K n) μ (arc1 k) v ∂κ = v := hp
    rw [e2] at e1
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun k => ?_)) e1
    simp [UnitaryRep.map_mul_apply, inner_smul_right]
  have hFx : FixF U₀ fun g => ⟪u, rightRegularRep (Gam K n) μ g v⟫_ℂ := by
    intro y hy g
    have h1 : rightRegularRep (Gam K n) μ (fin1 y) v = v := by
      have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv y) hy
      exact this
    have h2 : rightRegularRep (Gam K n) μ (g * fin1 y) v = rightRegularRep (Gam K n) μ g (rightRegularRep (Gam K n) μ (fin1 y) v) :=
      UnitaryRep.map_mul_apply _ g (fin1 y) v
    exact congrArg (fun z => ⟪u, z⟫_ℂ) (h2.trans (congrArg _ h1))
  have hfix := (hT.fix _ hc).2 ⟨hA, hFx⟩ 1
  rw [← integral_inner hintD]
  simp only [inner_smul_right]
  simpa using hfix

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Use `haveI := D.prob`. Establish `hU : IsCompact (D.U : Set (G1 K n))` using `(typeFin D).1`. Take `⟨L, hL⟩` from `lin_of (μ := μ) E hE`. Establish `hclosed : IsClosed (LinearMap.range L : Set (L2 μ))` using `Submodule.closed_of_finiteDimensional _`. It suffices to establish `hs : v ∈ LinearMap.range L by`.

Take `⟨φ, rfl⟩` from `hs`. Conclude with `⟨φ.1, φ.2, hL φ⟩`. Establish `hIP : ∀ w : L2 μ, Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k w) D.ν` using `fun w => integ_of hU D.supp (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit w))`. Establish `hIN : Integrable (fun k => ‖D.e k‖) D.ν` using `integ_of hU D.supp D.cont.norm`. Take `⟨C, hC⟩ : ∃ C : ℝ, C = (∫ k, ‖D.e k‖ ∂D.ν) + 1` from `⟨_, rfl⟩`.

Establish `hC0 : 0 < C`. Establish `: 0 ≤ ∫ k, ‖D.e k‖ ∂D.ν` using `integral_nonneg fun _ => norm_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPb : ∀ w : L2 μ, ‖(∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν) - v‖ ≤ C * ‖w - v‖`. Introduce `w`.

Use `conv_lhs => rw [← hPv]`. Rewrite using `[← integral_sub (hIP w) (hIP v)]`. Establish `: ‖∫ k, (D.e k • rightRegularRep (Gam K n) μ k w - D.e k • rightRegularRep (Gam K n) μ k v) ∂D.ν‖ ≤ ∫ k, ‖D.e k‖ * ‖w - v‖ ∂D.ν`. Use `norm_integral_le_of_norm_le (hIN.mul_const _) (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Rewrite using `[← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]`.

Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[integral_mul_const, hC]`. Use polynomial arithmetic with `[norm_nonneg (w - v)]`. Rewrite using `[← SetLike.mem_coe, ← hclosed.closure_eq, Metric.mem_closure_iff]`. Introduce `ε hε`.

Take `⟨f, hf⟩` from `approx (rightRegularRep (Gam K n) μ) μ v (div_pos hε (mul_pos two_pos hC0))`. Establish `hw : (rightRegularRep (Gam K n) μ).integrated μ (UnitaryRep.ccToL1 μ f) v ∈ τ` using `UnitaryRep.IsInvariant.integrated_mem _ μ hcl (fun g w hw => hinv g w hw) _ hv`. Take `⟨w, hwd⟩ : ∃ w, w = (rightRegularRep (Gam K n) μ).integrated μ (UnitaryRep.ccToL1 μ f) v` from `⟨_, rfl⟩`. Rewrite `hf`, `hw` using `[← hwd]`. Establish `hrep : IsContRep μ w (rconv (Gam K n) μ f v)` using `hwd ▸ isContRep_rconv μ f v`.

Establish `hz` using `avg_rep μ D.ν hU D.supp (j := id) continuous_id D.cont hrep`. Simplify using `only [id] at hz`. Establish `hzE` using `hmem _ hz.1 ⟨_, avg_mem hcl (hIP w) (fun k => τ.smul_mem _ (hinv k w hw)), hz.2.2⟩ (fix_avg D hrep.1)`. Use `⟨_, ⟨⟨_, hzE⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, show L ⟨_, hzE⟩ = ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν from rep_inj (hL ⟨_, hzE⟩) hz, norm_sub_rev]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem rep_in {τ : Submodule ℂ (L2 μ)} (hcl : IsClosed (τ : Set (L2 μ)))
    (hinv : ∀ g, ∀ v ∈ τ, rightRegularRep (Gam K n) μ g v ∈ τ) (D : TypeDat K n)
    (E : Submodule ℂ (G1 K n → ℂ)) [FiniteDimensional ℂ E] (hE : ∀ φ ∈ E, ∃ v : L2 μ, IsContRep μ v φ)
    (hmem : ∀ F : G1 K n → ℂ, Continuous F → (∃ v ∈ τ, Reps μ v F) → D.Fix F → F ∈ E) {v : L2 μ} (hv : v ∈ τ)
    (hPv : ∫ k, D.e k • rightRegularRep (Gam K n) μ k v ∂D.ν = v) : ∃ F ∈ E, IsContRep μ v F := by
  haveI := D.prob
  have hU : IsCompact (D.U : Set (G1 K n)) := (typeFin D).1
  obtain ⟨L, hL⟩ := lin_of (μ := μ) E hE
  have hclosed : IsClosed (LinearMap.range L : Set (L2 μ)) := Submodule.closed_of_finiteDimensional _
  suffices hs : v ∈ LinearMap.range L by
    obtain ⟨φ, rfl⟩ := hs
    exact ⟨φ.1, φ.2, hL φ⟩
  have hIP : ∀ w : L2 μ, Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k w) D.ν := fun w =>
    integ_of hU D.supp (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit w))
  have hIN : Integrable (fun k => ‖D.e k‖) D.ν := integ_of hU D.supp D.cont.norm
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (∫ k, ‖D.e k‖ ∂D.ν) + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    have : 0 ≤ ∫ k, ‖D.e k‖ ∂D.ν := integral_nonneg fun _ => norm_nonneg _
    linarith
  have hPb : ∀ w : L2 μ, ‖(∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν) - v‖ ≤ C * ‖w - v‖ := by
    intro w
    conv_lhs => rw [← hPv]
    rw [← integral_sub (hIP w) (hIP v)]
    have : ‖∫ k, (D.e k • rightRegularRep (Gam K n) μ k w - D.e k • rightRegularRep (Gam K n) μ k v) ∂D.ν‖ ≤
        ∫ k, ‖D.e k‖ * ‖w - v‖ ∂D.ν := by
      refine norm_integral_le_of_norm_le (hIN.mul_const _) (Eventually.of_forall fun k => ?_)
      rw [← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]
    refine this.trans ?_
    rw [integral_mul_const, hC]
    nlinarith [norm_nonneg (w - v)]
  rw [← SetLike.mem_coe, ← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, hf⟩ := approx (rightRegularRep (Gam K n) μ) μ v (div_pos hε (mul_pos two_pos hC0))
  have hw : (rightRegularRep (Gam K n) μ).integrated μ (UnitaryRep.ccToL1 μ f) v ∈ τ :=
    UnitaryRep.IsInvariant.integrated_mem _ μ hcl (fun g w hw => hinv g w hw) _ hv
  obtain ⟨w, hwd⟩ : ∃ w, w = (rightRegularRep (Gam K n) μ).integrated μ (UnitaryRep.ccToL1 μ f) v := ⟨_, rfl⟩
  rw [← hwd] at hf hw
  have hrep : IsContRep μ w (rconv (Gam K n) μ f v) := hwd ▸ isContRep_rconv μ f v
  have hz := avg_rep μ D.ν hU D.supp (j := id) continuous_id D.cont hrep
  simp only [id] at hz
  have hzE := hmem _ hz.1 ⟨_, avg_mem hcl (hIP w) (fun k => τ.smul_mem _ (hinv k w hw)), hz.2.2⟩ (fix_avg D hrep.1)
  refine ⟨_, ⟨⟨_, hzE⟩, rfl⟩, ?_⟩
  rw [dist_eq_norm, show L ⟨_, hzE⟩ = ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν from rep_inj (hL ⟨_, hzE⟩) hz, norm_sub_rev]
  calc _ ≤ C * ‖w - v‖ := hPb w
    _ ≤ C * (ε / (2 * C)) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end Proj

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/- English proof (translation)
Introduce `K _ _ _ μ _ τ κ p hτ hp S`. Establish `hmem` using `(xMem μ τ κ p hp).1 S`. Establish `hll` using `levLaws (K := K) 2 S`. Establish `hac : Continuous (arc1 : archCompact K 2 → G1 K 2)` using `hll.2.2.2.1`. Establish `hcp : CompactSpace (archCompact K 2)` using `hll.2.2.2.2.1`.

Use `haveI := hp.haar.prob`. Establish `hrep : ∀ φ ∈ Xs μ τ κ p S, ∃ v : L2 μ, IsContRep μ v φ` using `fun φ hφ => by`. Take `⟨hc, ⟨v, -, hr⟩, -, -⟩` from `(hmem φ).1 hφ`. Conclude with `⟨v, rep_of hc hr⟩`. Take `⟨J, hJ⟩` from `lin_of (μ := μ) (Xs μ τ κ p S) hrep`.

Establish `htr : ∀ {U₀ : Subgroup (FA K 2)} {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixF U₀ φ → ∀ u ∈ U₀, rightRegularRep (Gam K 2) μ (fin1 u) v = v`. Introduce `U₀ v φ h hF u hu`. Establish `h1` using `h.translate (fin1 u)`. Establish `e : (fun y => φ (y * fin1 u)) = φ` using `funext fun y => hF u hu y`. Rewrite `h1` using `[e]`.

Conclude with `rep_inj h1 h`. Establish `hfixv : ∀ {U₀ : Subgroup (FA K 2)} {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixF U₀ φ → v ∈ fixF μ U₀`. Introduce `U₀ v φ h hF`. Use `(Submodule.mem_iInf _).2 fun u => (Submodule.mem_iInf _).2 fun hu => ?_` and prove the remaining obligations. Conclude with `htr h hF u hu`.

Establish `havg : ∀ {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → IsContRep μ (pOp μ κ p v) (fun x => ∫ k, p k * φ (x * arc1 k) ∂κ)` using `fun h => avg_rep μ κ isCompact_univ (Eventually.of_forall fun _ => Set.mem_univ _) hac hp.cont h`. Establish `hpop : ∀ {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixA κ p φ → pOp μ κ p v = v`. Introduce `v φ h hA`. Establish `h1` using `havg h`. Establish `e : (fun x => ∫ k, p k * φ (x * arc1 k) ∂κ) = φ` using `funext hA`.

Rewrite `h1` using `[e]`. Conclude with `rep_inj h1 h`. Use `⟨J, fun a b hab => Subtype.ext ((hJ a).unique (hab ▸ hJ b)), fun φ => ?_, fun h φ φ' e => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Take `⟨hc, ⟨v, hv, hr⟩, hA, U, hU, hF⟩` from `(hmem φ.1).1 φ.2`. Use `⟨(hJ φ).2.2, ?_, hpop (hJ φ) hA, ?_⟩` and prove the remaining obligations.

Rewrite using `[rep_inj (hJ φ) (rep_of hc hr)]`. Conclude with `hv`. Establish `h1` using `hfixv (hJ φ) hF`. Rewrite `h1` using `[fixLev K 2 μ S U]`. Conclude with `h1.1`.

Establish `h1` using `(hJ φ).translate (fin1 h)`. Establish `e' : (fun y => φ.1 (y * fin1 h)) = φ'.1` using `funext fun x => (e x).symm`. Rewrite `h1` using `[e']`. Conclude with `rep_inj (hJ φ') h1`. Take `⟨hCO, hle⟩` from `hll.1 U hU`.

Take `⟨D, hD, -⟩` from `typeOf K 2 κ p hp (levOn S U) hle hCO.2`. Take `⟨-, hDK, 𝒜, hfd, h𝒜, hsl⟩` from `typeFin D`. Establish `hO : ∃ O : Set (G1 K 2), IsOpen O ∧ ∀ g ∈ KG K 2, g ∈ D.U ↔ g ∈ O`. Take `⟨O, hO, hUO⟩` from `D.isOpen`. Conclude with `⟨(fun g : G1 K 2 => (g : AdelicGLn.AdelicGL K 2)) ⁻¹' O, hO.preimage continuous_subtype_val, fun g hg => ⟨fun h => ((hUO g).1 h).1, fun h => (hUO g).2 ⟨h, hg⟩⟩⟩`.

Take `⟨E, hEf, hE1, hE2⟩` from `adm μ τ hτ D.U hDK hO 𝒜 hfd h𝒜`. Establish `hinE : ∀ F : G1 K 2 → ℂ, Continuous F → (∃ v ∈ τ, Reps μ v F) → D.Fix F → F ∈ E` using `fun F hc hr hf => hE2 F hc hr (hsl F hc hf)`. Use `haveI := hEf`. Use `⟨fun v hv hvf => ?_, E, hEf, fun φ hφ hF => ?_⟩` and prove the remaining obligations. Establish `hErep : ∀ φ ∈ E, ∃ v : L2 μ, IsContRep μ v φ` using `fun φ hφ => by`.

Take `⟨v, -, hr⟩` from `(hE1 φ hφ).rep`. Conclude with `⟨v, rep_of (hE1 φ hφ).cont hr⟩`. Take `⟨F, -, hFr⟩` from `rep_in hτ.closed hτ.inv D E hErep hinE hv.1 (fixed_of D hD hp hac hcp hv.2.1 hvf)`. Establish `hFA : FixA κ p F`. Establish `h1` using `havg hFr`.

Rewrite `h1` using `[hv.2.1]`. Conclude with `congrFun (h1.unique hFr)`. Establish `hFF : FixF (levOn S U) F`. Introduce `u hu`. Establish `h1` using `hFr.translate (fin1 u)`.

Establish `h2 : rightRegularRep (Gam K 2) μ (fin1 u) v = v` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hvf u) hu`. Rewrite `h1` using `[h2]`. Conclude with `congrFun (h1.unique hFr)`. Establish `hX : IsX μ τ κ p S F` using `⟨hFr.1, ⟨v, hv.1, hFr.2.2⟩, hFA, U, hU, hFF⟩`. Conclude with `⟨⟨F, (hmem F).2 hX⟩, rep_inj (hJ _) hFr, hFF⟩`.

Take `⟨hc, hr, hA, -⟩` from `(hmem φ).1 hφ`. Conclude with `hinE φ hc hr ((hD.fix φ hc).2 ⟨hA, hF⟩)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.exists_injection_into_l2_cusp :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → IdemA κ p → ∀ S : Finset (Pl K), ∃ J : Xs μ τ κ p S →ₗ[ℂ] L2 μ, Function.Injective J ∧ (∀ φ, Reps μ (J φ) φ ∧ InH μ τ κ p S (J φ)) ∧
      (∀ (h : FA K 2) (φ φ' : Xs μ τ κ p S), (∀ x, φ'.1 x = φ.1 (x * fin1 h)) → J φ' = rhoF μ h (J φ)) ∧
      ∀ U, Lev U → (∀ v, InH μ τ κ p S v → v ∈ fixF μ (levOn S U) → ∃ φ, J φ = v ∧ FixF (levOn S U) φ.1) ∧
        ∃ E : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E ∧ ∀ φ ∈ Xs μ τ κ p S, FixF (levOn S U) φ → φ ∈ E := by
  intro K _ _ _ μ _ τ κ p hτ hp S
  have hmem := (xMem μ τ κ p hp).1 S
  have hll := levLaws (K := K) 2 S
  have hac : Continuous (arc1 : archCompact K 2 → G1 K 2) := hll.2.2.2.1
  have hcp : CompactSpace (archCompact K 2) := hll.2.2.2.2.1
  haveI := hp.haar.prob
  have hrep : ∀ φ ∈ Xs μ τ κ p S, ∃ v : L2 μ, IsContRep μ v φ := fun φ hφ => by
    obtain ⟨hc, ⟨v, -, hr⟩, -, -⟩ := (hmem φ).1 hφ
    exact ⟨v, rep_of hc hr⟩
  obtain ⟨J, hJ⟩ := lin_of (μ := μ) (Xs μ τ κ p S) hrep
  have htr : ∀ {U₀ : Subgroup (FA K 2)} {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixF U₀ φ → ∀ u ∈ U₀,
      rightRegularRep (Gam K 2) μ (fin1 u) v = v := by
    intro U₀ v φ h hF u hu
    have h1 := h.translate (fin1 u)
    have e : (fun y => φ (y * fin1 u)) = φ := funext fun y => hF u hu y
    rw [e] at h1
    exact rep_inj h1 h
  have hfixv : ∀ {U₀ : Subgroup (FA K 2)} {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixF U₀ φ → v ∈ fixF μ U₀ := by
    intro U₀ v φ h hF
    refine (Submodule.mem_iInf _).2 fun u => (Submodule.mem_iInf _).2 fun hu => ?_
    exact htr h hF u hu
  have havg : ∀ {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ →
      IsContRep μ (pOp μ κ p v) (fun x => ∫ k, p k * φ (x * arc1 k) ∂κ) := fun h =>
    avg_rep μ κ isCompact_univ (Eventually.of_forall fun _ => Set.mem_univ _) hac hp.cont h
  have hpop : ∀ {v : L2 μ} {φ : G1 K 2 → ℂ}, IsContRep μ v φ → FixA κ p φ → pOp μ κ p v = v := by
    intro v φ h hA
    have h1 := havg h
    have e : (fun x => ∫ k, p k * φ (x * arc1 k) ∂κ) = φ := funext hA
    rw [e] at h1
    exact rep_inj h1 h
  refine ⟨J, fun a b hab => Subtype.ext ((hJ a).unique (hab ▸ hJ b)), fun φ => ?_, fun h φ φ' e => ?_, fun U hU => ?_⟩
  · obtain ⟨hc, ⟨v, hv, hr⟩, hA, U, hU, hF⟩ := (hmem φ.1).1 φ.2
    refine ⟨(hJ φ).2.2, ?_, hpop (hJ φ) hA, ?_⟩
    · rw [rep_inj (hJ φ) (rep_of hc hr)]
      exact hv
    · have h1 := hfixv (hJ φ) hF
      rw [fixLev K 2 μ S U] at h1
      exact h1.1
  · have h1 := (hJ φ).translate (fin1 h)
    have e' : (fun y => φ.1 (y * fin1 h)) = φ'.1 := funext fun x => (e x).symm
    rw [e'] at h1
    exact rep_inj (hJ φ') h1
  · obtain ⟨hCO, hle⟩ := hll.1 U hU
    obtain ⟨D, hD, -⟩ := typeOf K 2 κ p hp (levOn S U) hle hCO.2
    obtain ⟨-, hDK, 𝒜, hfd, h𝒜, hsl⟩ := typeFin D
    have hO : ∃ O : Set (G1 K 2), IsOpen O ∧ ∀ g ∈ KG K 2, g ∈ D.U ↔ g ∈ O := by
      obtain ⟨O, hO, hUO⟩ := D.isOpen
      exact ⟨(fun g : G1 K 2 => (g : AdelicGLn.AdelicGL K 2)) ⁻¹' O, hO.preimage continuous_subtype_val,
        fun g hg => ⟨fun h => ((hUO g).1 h).1, fun h => (hUO g).2 ⟨h, hg⟩⟩⟩
    obtain ⟨E, hEf, hE1, hE2⟩ := adm μ τ hτ D.U hDK hO 𝒜 hfd h𝒜
    have hinE : ∀ F : G1 K 2 → ℂ, Continuous F → (∃ v ∈ τ, Reps μ v F) → D.Fix F → F ∈ E :=
      fun F hc hr hf => hE2 F hc hr (hsl F hc hf)
    haveI := hEf
    refine ⟨fun v hv hvf => ?_, E, hEf, fun φ hφ hF => ?_⟩
    · have hErep : ∀ φ ∈ E, ∃ v : L2 μ, IsContRep μ v φ := fun φ hφ => by
        obtain ⟨v, -, hr⟩ := (hE1 φ hφ).rep
        exact ⟨v, rep_of (hE1 φ hφ).cont hr⟩
      obtain ⟨F, -, hFr⟩ := rep_in hτ.closed hτ.inv D E hErep hinE hv.1
        (fixed_of D hD hp hac hcp hv.2.1 hvf)
      have hFA : FixA κ p F := by
        have h1 := havg hFr
        rw [hv.2.1] at h1
        exact congrFun (h1.unique hFr)
      have hFF : FixF (levOn S U) F := by
        intro u hu
        have h1 := hFr.translate (fin1 u)
        have h2 : rightRegularRep (Gam K 2) μ (fin1 u) v = v :=
          (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hvf u) hu
        rw [h2] at h1
        exact congrFun (h1.unique hFr)
      have hX : IsX μ τ κ p S F := ⟨hFr.1, ⟨v, hv.1, hFr.2.2⟩, hFA, U, hU, hFF⟩
      exact ⟨⟨F, (hmem F).2 hX⟩, rep_inj (hJ _) hFr, hFF⟩
    · obtain ⟨hc, hr, hA, -⟩ := (hmem φ).1 hφ
      exact hinE φ hc hr ((hD.fix φ hc).2 ⟨hA, hF⟩)
