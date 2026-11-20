import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing InnerProductSpace ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

/- English proof (translation)
Use `set C : normOneGL K n → ℂ := fun x => c (mk Γ₁ x) with hCdef`. Establish `hCm : StronglyMeasurable C` using `stronglyMeasurable_lift Γ₁ μ c`. Establish `h1 : ∀ g : normOneGL K n, ∀ᵐ x ∂μ, C (x * g) = C x`. Introduce `g`. Establish `h` using `coeFn_rightRegularRep Γ₁ μ g c`.

Rewrite `h` using `[hc g]`. Establish `h2` using `(quasiMeasurePreserving_mk Γ₁ μ).ae h`. Use `filter_upwards [h2] with x hx`. Rewrite `hx` using `[rightMul_mk]`. Conclude with `hx.symm`.

Establish `hset : MeasurableSet {p : normOneGL K n × normOneGL K n | C (p.1 * p.2) = C p.1}` using `measurableSet_eq_fun (hCm.measurable.comp continuous_mul.measurable) (hCm.measurable.comp measurable_fst)`. Establish `h2 : ∀ᵐ x ∂μ, ∀ᵐ g ∂μ, C (x * g) = C x` using `(Measure.ae_ae_comm hset).2 (ae_of_all _ h1)`. Establish `: (ae μ).NeBot` using `ae_neBot.2 (NeZero.ne μ)`. Take `⟨x₀, hx₀⟩` from `h2.exists`. Use `⟨C x₀, ?_⟩` and prove the remaining obligations.

Establish `h3 : ∀ᵐ y ∂μ, C y = C x₀`. Establish `h4 : μ {y | ¬ C y = C x₀} = 0`. Rewrite using `[← measure_preimage_mul μ x₀]`. Conclude with `ae_iff.1 hx₀`. Conclude with `ae_iff.2 h4`.

Establish `hmeas : MeasurableSet {q : RightCosetSpace Γ₁ | c q = C x₀}` using `measurableSet_eq_fun (Lp.stronglyMeasurable c).measurable measurable_const`. Express the relevant statement in the definitionally equal form `∀ᵐ q ∂(Measure.map (mk Γ₁) (μ.restrict (fundamentalDomain Γ₁))), c q = C x₀`. Rewrite using `[ae_map_iff (measurable_mk Γ₁).aemeasurable hmeas]`. Conclude with `ae_restrict_of_ae h3`.
-/
theorem exists_ae_eq_const_of_forall_eq {c : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hc : ∀ g, rightRegularRep Γ₁ μ g c = c) :
    ∃ κ : ℂ, (c : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] fun _ => κ := by
  set C : normOneGL K n → ℂ := fun x => c (mk Γ₁ x) with hCdef
  have hCm : StronglyMeasurable C := stronglyMeasurable_lift Γ₁ μ c
  have h1 : ∀ g : normOneGL K n, ∀ᵐ x ∂μ, C (x * g) = C x := by
    intro g
    have h := coeFn_rightRegularRep Γ₁ μ g c
    rw [hc g] at h
    have h2 := (quasiMeasurePreserving_mk Γ₁ μ).ae h
    filter_upwards [h2] with x hx
    rw [rightMul_mk] at hx
    exact hx.symm
  have hset : MeasurableSet {p : normOneGL K n × normOneGL K n | C (p.1 * p.2) = C p.1} :=
    measurableSet_eq_fun (hCm.measurable.comp continuous_mul.measurable)
      (hCm.measurable.comp measurable_fst)
  have h2 : ∀ᵐ x ∂μ, ∀ᵐ g ∂μ, C (x * g) = C x :=
    (Measure.ae_ae_comm hset).2 (ae_of_all _ h1)
  have : (ae μ).NeBot := ae_neBot.2 (NeZero.ne μ)
  obtain ⟨x₀, hx₀⟩ := h2.exists
  refine ⟨C x₀, ?_⟩
  have h3 : ∀ᵐ y ∂μ, C y = C x₀ := by
    have h4 : μ {y | ¬ C y = C x₀} = 0 := by
      rw [← measure_preimage_mul μ x₀]
      exact ae_iff.1 hx₀
    exact ae_iff.2 h4
  have hmeas : MeasurableSet {q : RightCosetSpace Γ₁ | c q = C x₀} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable c).measurable measurable_const
  change ∀ᵐ q ∂(Measure.map (mk Γ₁) (μ.restrict (fundamentalDomain Γ₁))), c q = C x₀
  rw [ae_map_iff (measurable_mk Γ₁).aemeasurable hmeas]
  exact ae_restrict_of_ae h3

/- English proof (translation)
Establish `h1` using `(hc : IsCuspidalL2 μ c) 1 one_pos (by omega)`. Establish `h2` using `ae_ctFun_congr μ 1 hκ`. Establish `h3 : ∀ y, ctFun K n 1 (fun _ : RightCosetSpace Γ₁ => κ) y = κ`. Introduce `y`. Simplify using `only [ctFun]`.

Rewrite using `[setIntegral_const, measureReal_def, unipMeasure_unipFundamentalDomain]`. Simplify using the standard rewrite rules. Establish `: (ae μ).NeBot` using `ae_neBot.2 (NeZero.ne μ)`. Take `⟨y, hy1, hy2⟩` from `(h1.and h2).exists`. Rewrite `hy1` using `[Pi.zero_apply, constantTermL2, hy2, h3]`.

Conclude with `hy1`.
-/
theorem eq_zero_of_ae_eq_const (hn : 2 ≤ n) {c : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hc : c ∈ cuspidalL2 μ) {κ : ℂ}
    (hκ : (c : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] fun _ => κ) : κ = 0 := by
  have h1 := (hc : IsCuspidalL2 μ c) 1 one_pos (by omega)
  have h2 := ae_ctFun_congr μ 1 hκ
  have h3 : ∀ y, ctFun K n 1 (fun _ : RightCosetSpace Γ₁ => κ) y = κ := by
    intro y
    simp only [ctFun]
    rw [setIntegral_const, measureReal_def, unipMeasure_unipFundamentalDomain]
    simp
  have : (ae μ).NeBot := ae_neBot.2 (NeZero.ne μ)
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  rw [Pi.zero_apply, constantTermL2, hy2, h3] at hy1
  exact hy1

/- English proof (translation)
Use `Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Take `⟨C, hC⟩` from `hbd`. Use `MemLp.of_bound (continuous_cuspQuot _ hψc).aestronglyMeasurable C (Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`. Conclude with `hC y y.2`.
-/
theorem memLp_cuspQuot_of_bounded {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    (hψl : IsLeftInvariant ψ) (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C) :
    MemLp (cuspQuot hψl) 2 (quotientMeasure Γ₁ μ) := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨C, hC⟩ := hbd
  refine MemLp.of_bound (continuous_cuspQuot _ hψc).aestronglyMeasurable C
    (Eventually.of_forall fun q => ?_)
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  exact hC y y.2

/- English proof (translation)
Introduce `r hr hrn`. Use `filter_upwards [ae_ctFun_congr μ r (MemLp.coeFn_toLp (memLp_cuspQuot_of_bounded μ hψc hψl hbd))] with y hy`. Rewrite using `[constantTermL2, hy]`. Conclude with `hψ r hr hrn y`.
-/
theorem toLp_cuspQuot_mem_cuspidalL2 {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ) (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C) :
    (memLp_cuspQuot_of_bounded μ hψc hψl hbd).toLp _ ∈ cuspidalL2 μ := by
  intro r hr hrn
  filter_upwards [ae_ctFun_congr μ r (MemLp.coeFn_toLp (memLp_cuspQuot_of_bounded μ hψc hψl hbd))]
    with y hy
  rw [constantTermL2, hy]
  exact hψ r hr hrn y

/- English proof (translation)
Use `Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `: CompleteSpace (cuspidalL2 μ)` using `(isClosed_cuspidalL2 μ).completeSpace_coe`. Establish `hmem` using `memLp_cuspQuot_of_bounded μ hψc hψl hbd`. Establish `hvS : hmem.toLp _ ∈ cuspidalL2 μ` using `toLp_cuspQuot_mem_cuspidalL2 μ hψc hψl hψ hbd`. Establish `hone` using `memLp_const (μ := quotientMeasure Γ₁ μ) (p := 2) (1 : ℂ)`.

Establish `e1 : ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) ∂μ = ∫ q, cuspQuot hψl q ∂quotientMeasure Γ₁ μ`. Rewrite using `[integral_quotientMeasure]`. Both sides reduce to the same expression. Establish `hint : ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) ∂μ = ⟪hone.toLp _, hmem.toLp _⟫_ℂ`. Rewrite using `[e1, MeasureTheory.L2.inner_def]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [MemLp.coeFn_toLp hmem, MemLp.coeFn_toLp hone] with q h1 h2`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Establish `hR1 : ∀ g, rightRegularRep Γ₁ μ g (hone.toLp _) = hone.toLp _`.

Introduce `g`. Use `Lp.ext ?_` and prove the remaining obligations. Establish `h1` using `coeFn_rightRegularRep Γ₁ μ g (hone.toLp _)`. Establish `h2 : (fun x => (hone.toLp _ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (rightMul Γ₁ g x)) =ᵐ[quotientMeasure Γ₁ μ] fun _ => (1 : ℂ)` using `(measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq (MemLp.coeFn_toLp hone)`. Conclude with `h1.trans (h2.trans (MemLp.coeFn_toLp hone).symm)`.

Establish `hcomm` using `((rightRegularRep Γ₁ μ).isInvariant_iff_commute_starProjection (cuspidalL2 μ)).1 (isInvariant_cuspidalL2 μ)`. Establish `hcinv : ∀ g, rightRegularRep Γ₁ μ g ((cuspidalL2 μ).starProjection (hone.toLp _)) = (cuspidalL2 μ).starProjection (hone.toLp _)`. Introduce `g`. Establish `h : rightRegularRep Γ₁ μ g ((cuspidalL2 μ).starProjection (hone.toLp _)) = (cuspidalL2 μ).starProjection (rightRegularRep Γ₁ μ g (hone.toLp _))` using `congrArg (fun T : Lp ℂ 2 (quotientMeasure Γ₁ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) => T (hone.toLp _)) (hcomm g).eq`. Rewrite using `[h, hR1 g]`.

Take `⟨κ, hκ⟩` from `exists_ae_eq_const_of_forall_eq μ hcinv`. Establish `hκ0 : κ = 0` using `eq_zero_of_ae_eq_const μ hn ((cuspidalL2 μ).starProjection_apply_mem (hone.toLp _)) hκ`. Establish `hc0 : (cuspidalL2 μ).starProjection (hone.toLp _) = 0`. Use `Lp.ext (hκ.trans ?_)` and prove the remaining obligations. Rewrite using `[hκ0]`.

Conclude with `(Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ)).symm`. Rewrite using `[hint, ← Submodule.starProjection_eq_self_iff.2 hvS, ← Submodule.inner_starProjection_left_eq_right, hc0, inner_zero_left]`.
-/
theorem setIntegral_fundamentalDomain_eq_zero (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hbd : ∃ C, ∀ g ∈ normOneGL K n, ‖ψ g‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) ∂μ = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have : CompleteSpace (cuspidalL2 μ) := (isClosed_cuspidalL2 μ).completeSpace_coe
  have hmem := memLp_cuspQuot_of_bounded μ hψc hψl hbd
  have hvS : hmem.toLp _ ∈ cuspidalL2 μ := toLp_cuspQuot_mem_cuspidalL2 μ hψc hψl hψ hbd
  have hone := memLp_const (μ := quotientMeasure Γ₁ μ) (p := 2) (1 : ℂ)

  have e1 : ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) ∂μ =
      ∫ q, cuspQuot hψl q ∂quotientMeasure Γ₁ μ := by
    rw [integral_quotientMeasure]
    rfl
  have hint : ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) ∂μ =
      ⟪hone.toLp _, hmem.toLp _⟫_ℂ := by
    rw [e1, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hmem, MemLp.coeFn_toLp hone] with q h1 h2
    rw [h1, h2]
    simp

  have hR1 : ∀ g, rightRegularRep Γ₁ μ g (hone.toLp _) = hone.toLp _ := by
    intro g
    refine Lp.ext ?_
    have h1 := coeFn_rightRegularRep Γ₁ μ g (hone.toLp _)
    have h2 : (fun x => (hone.toLp _ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (rightMul Γ₁ g x))
        =ᵐ[quotientMeasure Γ₁ μ] fun _ => (1 : ℂ) :=
      (measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq (MemLp.coeFn_toLp hone)
    exact h1.trans (h2.trans (MemLp.coeFn_toLp hone).symm)

  have hcomm := ((rightRegularRep Γ₁ μ).isInvariant_iff_commute_starProjection (cuspidalL2 μ)).1
    (isInvariant_cuspidalL2 μ)
  have hcinv : ∀ g, rightRegularRep Γ₁ μ g ((cuspidalL2 μ).starProjection (hone.toLp _)) =
      (cuspidalL2 μ).starProjection (hone.toLp _) := by
    intro g
    have h : rightRegularRep Γ₁ μ g ((cuspidalL2 μ).starProjection (hone.toLp _)) =
        (cuspidalL2 μ).starProjection (rightRegularRep Γ₁ μ g (hone.toLp _)) :=
      congrArg (fun T : Lp ℂ 2 (quotientMeasure Γ₁ μ) →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) =>
        T (hone.toLp _)) (hcomm g).eq
    rw [h, hR1 g]
  obtain ⟨κ, hκ⟩ := exists_ae_eq_const_of_forall_eq μ hcinv
  have hκ0 : κ = 0 :=
    eq_zero_of_ae_eq_const μ hn ((cuspidalL2 μ).starProjection_apply_mem (hone.toLp _)) hκ
  have hc0 : (cuspidalL2 μ).starProjection (hone.toLp _) = 0 := by
    refine Lp.ext (hκ.trans ?_)
    rw [hκ0]
    exact (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ)).symm
  rw [hint, ← Submodule.starProjection_eq_self_iff.2 hvS,
    ← Submodule.inner_starProjection_left_eq_right, hc0, inner_zero_left]

end GJGlobal

end

end GroundTheory.Automorphic
