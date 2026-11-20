import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
import Formalism.LatticeTheta.ThetaShiftInversion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoKernelPhiLineContinuousIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeWeightTwoLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompactStatement

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.HeckeTwoPoisson

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR

/- English proof (translation)
The claim follows from `GlobalTheory.T.heckePhiFourierTransform_rapid_decay`.
-/
theorem hTrans_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := GlobalTheory.T.heckePhiFourierTransform_rapid_decay

/- English proof (translation)
The claim follows from `GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable`.
-/
theorem phi_line : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
    Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable

/- English proof (translation)
The claim follows from `GlobalTheory.T.summable_heckeWeightTwoLatticeSum`.
-/
theorem summable_lat : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} =>
      ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := GlobalTheory.T.summable_heckeWeightTwoLatticeSum

/- English proof (translation)
The claim follows from `GlobalTheory.T.prod_rpow_decay_isBigO_cocompact'`.
-/
theorem prod_isBigO : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b →
    (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) →
    (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)]
      (fun v => ‖v‖ ^ (-b)) := GlobalTheory.T.prod_rpow_decay_isBigO_cocompact'

/- English proof (translation)
Simplify using `only [Real.fourier_eq', Real.fourier_real_eq]`. Rewrite using `[← integral_fintype_prod_volume_eq_prod, ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]`.
-/
theorem fourier_prod (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

/- English proof (translation)
Introduce `a b h`. Establish `hne : Nonempty (F →+* ℝ)`. Rewrite using `[← Fintype.card_pos_iff, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb]`. Conclude with `Module.finrank_pos`. Establish `h1` using `congrArg (fun v : RSp F => v (Classical.choice hne)) h`.

Simplify using `only [remb_apply] at h1`. Conclude with `(Classical.choice hne).injective h1`.
-/
theorem remb_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

/- English proof (translation)
Use function extensionality and compare the values at `ν`. Rewrite using `[Real.fourier_real_eq]`. Unfold `hTrans`. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Real.fourierChar_apply]`.

Rewrite using `[mul_comm]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTrans_eq_fourier (σ : ℂ) (y : ℝ) :
    (fun ν : ℝ => hTrans σ ν y) = 𝓕 (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) := by
  funext ν
  rw [Real.fourier_real_eq]
  unfold hTrans
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Real.fourierChar_apply]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/- English proof (translation)
Rewrite using `[hTrans_eq_fourier]`. Conclude with `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (phi_line σ hσ y hy).2`.
-/
theorem continuous_hTrans (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun ν : ℝ => hTrans σ ν y) := by
  rw [hTrans_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (phi_line σ hσ y hy).2

/- English proof (translation)
Use `set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf`. Take `⟨hfc, hfi⟩` from `phi_line σ hσ y hy`. Establish `hH` using `hTrans_eq_fourier σ y`. Establish `hFi : Integrable (𝓕 f)`. Take `⟨C, hC⟩` from `hTrans_decay σ hσ y hy 2`.

Establish `h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ)))` using `integrable_one_add_norm (by simp)`. Use `(h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Rewrite using `[← hH]`. Conclude with `(continuous_hTrans σ hσ y hy).aestronglyMeasurable`. Use `hC t` as an intermediate fact.

Rewrite using `[← hH]`. Simplify `this` using `[Real.norm_eq_abs]`. Establish `hinv : 𝓕⁻ (𝓕 f) = f` using `Continuous.fourierInv_fourier_eq hfc hfi hFi`. Establish `hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s = 𝓕 (𝓕 f) (s - c)`. Rewrite using `[Real.fourier_real_eq, Real.fourier_real_eq, ← hH]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmod]`. Establish `h3` using `congrFun hinv (-(s - c))`. Rewrite `h3` using `[Real.fourierInv_eq_fourier_neg, neg_neg]`. Rewrite using `[h3, hf]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_mod (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (c s : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      phi σ (((c - s : ℝ) : ℂ) + (y : ℂ) * I) := by
  set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf
  obtain ⟨hfc, hfi⟩ := phi_line σ hσ y hy
  have hH := hTrans_eq_fourier σ y
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, hC⟩ := hTrans_decay σ hσ y hy 2
    have h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine (h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · rw [← hH]; exact (continuous_hTrans σ hσ y hy).aestronglyMeasurable
    · have := hC t
      rw [← hH]
      simpa [Real.norm_eq_abs] using this
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi
  have hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      𝓕 (𝓕 f) (s - c) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmod]
  have h3 := congrFun hinv (-(s - c))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h3
  rw [h3, hf]
  congr 2
  push_cast
  ring

/- English proof (translation)
Introduce `F _ _ _ 𝔞 σ hσ z hz b hb`. Use `set A : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) with hA`. Establish `hA0 : A ≠ 0` using `𝔞.ne_zero`. Use `haveI : DiscreteTopology (latOf A) := discrete_latOf F A`. Use `haveI : IsZLattice ℝ (latOf A) := isZLattice_latOf F A hA0`.

Use `set L := latOf A with hL`. Establish `hdual : Formalism.H.dual L = latOf (latM 𝔞)`. Rewrite using `[hL, dual_latOf_eq_latOf_traceDual F A hA0, latM_eq_dual]`. Establish `hcov : ZLattice.covolume L = omegaFactor 𝔞`. Rewrite using `[hL, GlobalTheory.LipschitzCovol.covolume_latOf F A hA0, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol, omegaFactor, dF, nrm, Real.sqrt_eq_rpow]`.

Take `⟨h1, h2⟩` from `Formalism.H.dualIsLattice (RSp F) L`. Use `haveI : DiscreteTopology (Formalism.H.dual L) := h1`. Establish `hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0` using `fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'`. Use `set g : Emb F → ℝ → ℂ := fun τ t => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) * hTrans σ t (τ b * (z τ).im) with hg`. Use `set Ψ : RSp F → ℂ := fun v => ∏ τ, g τ (v τ) with hΨ`.

Establish `hΨν : ∀ ν : F, Ψ (remb F ν) = fTerm σ z b ν`. Introduce `ν`. Simplify using `only [hΨ, hg, remb_apply, fTerm]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 3`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hgn : ∀ τ t, ‖g τ t‖ = ‖hTrans σ t (τ b * (z τ).im)‖`. Introduce `τ t`. Simplify using `only [hg, norm_mul]`.

Rewrite using `[show (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) = ((2 * Real.pi * (t * (τ b * (z τ).re)) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]`. Establish `hΨc : Continuous Ψ`. Use `continuous_finset_prod _ fun τ _ => ?_` and prove the remaining obligations. Use `Continuous.comp (g := g τ) ?_ ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)` and prove the remaining obligations. Conclude with `(by fun_prop : Continuous fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ))).mul (continuous_hTrans σ hσ _ (hyτ τ))`.

Use `set N : ℕ := Module.finrank ℝ (RSp F) + 1 with hN`. Establish `hbN : (Module.finrank ℝ (RSp F) : ℝ) < (N : ℝ)` using `by rw [hN]; push_cast; linarith`. Establish `hΨO : Ψ =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-(N : ℝ))` using `prod_isBigO (Emb F) g N (Nat.cast_nonneg _) fun τ => by`. Take `⟨C, hC⟩` from `hTrans_decay σ hσ _ (hyτ τ) N`. Conclude with `⟨C, fun t => (hgn τ t).symm ▸ hC t⟩`.

Take `⟨hint, hsumx, hGc, hGper⟩` from `Formalism.H.poisson_periodization (RSp F) L Ψ hΨc (N : ℝ) hbN hΨO`. Use `haveI : Module.Free ℤ L := ZLattice.module_free ℝ L`. Use `haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L`. Establish `hD` using `ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))`. Use `set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)`.

Establish `hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 Ψ μ` using `fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L Ψ hint D hD μ μ.2`. Establish `hFΨ : ∀ a : F, 𝓕 Ψ (remb F (-a)) = ∏ τ : Emb F, phi σ (((τ a : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)`. Introduce `a`. Rewrite using `[hΨ, fourier_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[remb_apply, hg]`. Simplify using `only`. Rewrite using `[fourier_mod σ hσ _ (hyτ τ)]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.

Establish `hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ latM 𝔞, remb F a = x`. Introduce `x`. Rewrite using `[hdual]`. Conclude with `mem_latOf _ x`. Establish `hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ A, remb F ν = x`.

Introduce `x`. Rewrite using `[hL]`. Conclude with `mem_latOf _ x`. Set `eM : {a : F // a ∈ latM 𝔞} ≃ Formalism.H.dual L` to `Equiv.ofBijective (fun a => ⟨remb F (-a.1), (hDmem _).2 ⟨-a.1, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem a.2, rfl⟩⟩) ⟨fun a a' h => Subtype.ext (neg_injective (remb_inj (congrArg Subtype.val h))), fun μ => by`. Take `⟨a, ha, h⟩` from `(hDmem μ).1 μ.2`.

Conclude with `⟨⟨-a, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem ha⟩, Subtype.ext (by simp [h])⟩⟩`. Set `eD : {ν : F // ν ∈ A} ≃ L` to `Equiv.ofBijective (fun ν => ⟨remb F ν.1, (hLmem _).2 ⟨ν.1, ν.2, rfl⟩⟩) ⟨fun ν ν' h => Subtype.ext (remb_inj (congrArg Subtype.val h)), fun μ => by`. Take `⟨ν, hν, h⟩` from `(hLmem μ).1 μ.2`. Conclude with `⟨⟨ν, hν⟩, Subtype.ext h⟩⟩`. Establish `hsL` using `summable_lat F 𝔞 σ hσ z hz b hb`.

Establish `hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) * Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ))))`. Simplify using `only [hcoef]`. Rewrite using `[← eM.summable_iff]`. Conclude with `hsL.congr fun a => (hFΨ a.1).symm`. Establish `H4` using `Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Ψ ((l : RSp F) + x)) hGc hGper D hD hsumc 0`.

Simplify using `only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, add_zero] at H4`. Rewrite `H4` using `[← eM.hasSum_iff]`. Establish `hs0 : Summable (fun l : L => Ψ (l : RSp F))` using `by simpa using hsumx 0`. Establish `hsF : Summable (fun ν : {ν : F // ν ∈ A} => fTerm σ z b ν.1)`. Rewrite `hs0` using `[← eD.summable_iff]`.

Conclude with `hs0.congr fun ν => hΨν ν.1`. Establish `hR : ∑' l : L, Ψ (l : RSp F) = ∑' ν : {ν : F // ν ∈ A}, fTerm σ z b ν.1`. Rewrite using `[← eD.tsum_eq]`. Conclude with `tsum_congr fun ν => hΨν ν.1`. Use `⟨hsF, ?_⟩` and prove the remaining obligations.

Establish `hc0 : (ZLattice.covolume L : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero L volume)`. Establish `H5` using `H4.mul_left (ZLattice.covolume L : ℂ)`. Rewrite `H5` using `[hR]`. Rewrite using `[← hcov]`. Use `H5.congr_fun fun a => ?_` and prove the remaining obligations.

Establish `key : ∀ a : {a : F // a ∈ latM 𝔞}, 𝓕 Ψ ((eM a : RSp F)) = ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)` using `fun a => hFΨ a.1`. Simplify using `only [Function.comp_apply, key]`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`.
-/
theorem poisson : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ),
    0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧
    HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ))
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  intro F _ _ _ 𝔞 σ hσ z hz b hb
  classical
  set A : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) with hA
  have hA0 : A ≠ 0 := 𝔞.ne_zero
  haveI : DiscreteTopology (latOf A) := discrete_latOf F A
  haveI : IsZLattice ℝ (latOf A) := isZLattice_latOf F A hA0
  set L := latOf A with hL
  have hdual : Formalism.H.dual L = latOf (latM 𝔞) := by
    rw [hL, dual_latOf_eq_latOf_traceDual F A hA0, latM_eq_dual]
  have hcov : ZLattice.covolume L = omegaFactor 𝔞 := by
    rw [hL, GlobalTheory.LipschitzCovol.covolume_latOf F A hA0, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol, omegaFactor, dF, nrm,
      Real.sqrt_eq_rpow]
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) L
  haveI : DiscreteTopology (Formalism.H.dual L) := h1

  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  set g : Emb F → ℝ → ℂ := fun τ t =>
    Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) * hTrans σ t (τ b * (z τ).im) with hg
  set Ψ : RSp F → ℂ := fun v => ∏ τ, g τ (v τ) with hΨ
  have hΨν : ∀ ν : F, Ψ (remb F ν) = fTerm σ z b ν := by
    intro ν
    simp only [hΨ, hg, remb_apply, fTerm]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 3
    push_cast
    ring
  have hgn : ∀ τ t, ‖g τ t‖ = ‖hTrans σ t (τ b * (z τ).im)‖ := by
    intro τ t
    simp only [hg, norm_mul]
    rw [show (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) =
      ((2 * Real.pi * (t * (τ b * (z τ).re)) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hΨc : Continuous Ψ := by
    refine continuous_finset_prod _ fun τ _ => ?_
    refine Continuous.comp (g := g τ) ?_ ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ))).mul
      (continuous_hTrans σ hσ _ (hyτ τ))
  set N : ℕ := Module.finrank ℝ (RSp F) + 1 with hN
  have hbN : (Module.finrank ℝ (RSp F) : ℝ) < (N : ℝ) := by rw [hN]; push_cast; linarith
  have hΨO : Ψ =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-(N : ℝ)) :=
    prod_isBigO (Emb F) g N (Nat.cast_nonneg _) fun τ => by
      obtain ⟨C, hC⟩ := hTrans_decay σ hσ _ (hyτ τ) N
      exact ⟨C, fun t => (hgn τ t).symm ▸ hC t⟩
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L Ψ hΨc (N : ℝ) hbN hΨO
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 Ψ μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L Ψ hint D hD μ μ.2

  have hFΨ : ∀ a : F, 𝓕 Ψ (remb F (-a)) = ∏ τ : Emb F, phi σ (((τ a : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) := by
    intro a
    rw [hΨ, fourier_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [remb_apply, hg]
    simp only
    rw [fourier_mod σ hσ _ (hyτ τ)]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ latM 𝔞, remb F a = x := by
    intro x; rw [hdual]; exact mem_latOf _ x
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ A, remb F ν = x := by
    intro x; rw [hL]; exact mem_latOf _ x
  let eM : {a : F // a ∈ latM 𝔞} ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F (-a.1), (hDmem _).2 ⟨-a.1, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem a.2, rfl⟩⟩)
    ⟨fun a a' h => Subtype.ext (neg_injective (remb_inj (congrArg Subtype.val h))), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨-a, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem ha⟩, Subtype.ext (by simp [h])⟩⟩
  let eD : {ν : F // ν ∈ A} ≃ L := Equiv.ofBijective
    (fun ν => ⟨remb F ν.1, (hLmem _).2 ⟨ν.1, ν.2, rfl⟩⟩)
    ⟨fun ν ν' h => Subtype.ext (remb_inj (congrArg Subtype.val h)), fun μ => by
      obtain ⟨ν, hν, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨ν, hν⟩, Subtype.ext h⟩⟩
  have hsL := summable_lat F 𝔞 σ hσ z hz b hb
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact hsL.congr fun a => (hFΨ a.1).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Ψ ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have hs0 : Summable (fun l : L => Ψ (l : RSp F)) := by simpa using hsumx 0
  have hsF : Summable (fun ν : {ν : F // ν ∈ A} => fTerm σ z b ν.1) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hΨν ν.1
  have hR : ∑' l : L, Ψ (l : RSp F) = ∑' ν : {ν : F // ν ∈ A}, fTerm σ z b ν.1 := by
    rw [← eD.tsum_eq]
    exact tsum_congr fun ν => hΨν ν.1
  refine ⟨hsF, ?_⟩
  have hc0 : (ZLattice.covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero L volume)
  have H5 := H4.mul_left (ZLattice.covolume L : ℂ)
  rw [hR] at H5
  rw [← hcov]
  refine H5.congr_fun fun a => ?_
  have key : ∀ a : {a : F // a ∈ latM 𝔞}, 𝓕 Ψ ((eM a : RSp F)) = ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) :=
    fun a => hFΨ a.1
  simp only [Function.comp_apply, key]
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.HeckeTwoPoisson
