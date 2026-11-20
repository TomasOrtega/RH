import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHaarMeasureComapSubtype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionTestVectorBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzZetaSeparatingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticCharacterNormGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilConstantQuadraticCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormGroupIndexTwoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzNormFormPullbackStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantSquareStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantNormOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousEqOfSchwartzPairingStatement
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.GaussLam

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0 w`. Establish `hcE : Continuous (chE E χ)` using `GroundTheory.LocalField.continuous_traceChar hχ hχ1`. Establish `hnE : chE E χ ≠ 1` using `GroundTheory.LocalField.traceChar_ne_one hχ hχ1`. Establish `hf` using `localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg`. Establish `hΨ` using `GlobalTheory.T.schwartz_norm_form_pullback F E _ hf`.

Establish `hFΨ` using `localFourier_mem_schwartzBruhat (muE E χ) hcE hnE hΨ`. Establish `hσ1 : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E`. Break down `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h` into its components or cases. Conclude with `absurd h hσ`. Conclude with `h`.

Establish `hσc : Continuous σ.symm`. Establish `: (σ.symm : E → E) = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E`. Use function extensionality and compare the values at `x`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply, hσ1, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj_conj]`.

Rewrite using `[this]`. Conclude with `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj`. Establish `hgt` using `(GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0).1`. Establish `hh : Continuous (GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g)`. Establish `e : GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g = localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g)`.

Use function extensionality and compare the values at `fun t => (GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0 t).symm`. Rewrite using `[e]`. Conclude with `(localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt).1.continuous`. Establish `hP` using `hFΨ.1.continuous.comp hσc`. Establish `hQ : Continuous fun z : E => γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z)` using `continuous_const.mul (hh.comp (GlobalTheory.T.continuous_algebra_norm F E))`.

Establish `key` using `GlobalTheory.T.continuous_eq_of_schwartz_pairing E (muE E χ) _ _ hP hQ (fun Φ hΦ => by`. Simplify using `only [Function.comp_apply]`. Rewrite using `[← GlobalTheory.T.weil_gauss_constant_square F E χ hχ hχ1 σ Φ hΦ g hg]`. Establish `e2 : ∫ z, Φ z * (γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z)) ∂muE E χ = γ * ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, ← GlobalTheory.T.weil_gauss_constant_norm_one F E χ hχ hχ1 η hcη hη Φ hΦ g hg g0, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations.

Simplify using `only`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using `[g0]`. Use `hγ (Units.mk0 a ha) Φ hΦ` as an intermediate fact.

Simplify using `only [Units.val_mk0] at this`. Rewrite using `[this]`. Use the proof step `ring)`. Establish `h1` using `congrFun key (σ w)`. Simplify using `only [Function.comp_apply, AlgEquiv.symm_apply_apply] at h1`.

Rewrite using `[h1, Algebra.norm_eq_of_algEquiv]`.
-/
theorem ptw : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ γ : ℂ, (∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ = γ * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ w : E, localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) w = γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F w) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0 w
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf
  have hFΨ := localFourier_mem_schwartzBruhat (muE E χ) hcE hnE hΨ
  have hσ1 : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
    rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h
    · exact absurd h hσ
    · exact h
  have hσc : Continuous σ.symm := by
    have : (σ.symm : E → E) = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
      funext x
      apply σ.injective
      rw [AlgEquiv.apply_symm_apply, hσ1, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj_conj]
    rw [this]
    exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj
  have hgt := (GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0).1
  have hh : Continuous (GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g) := by
    have e : GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g = localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) :=
      funext fun t => (GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0 t).symm
    rw [e]
    exact (localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt).1.continuous
  have hP := hFΨ.1.continuous.comp hσc
  have hQ : Continuous fun z : E => γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) :=
    continuous_const.mul (hh.comp (GlobalTheory.T.continuous_algebra_norm F E))
  have key := GlobalTheory.T.continuous_eq_of_schwartz_pairing E (muE E χ) _ _ hP hQ (fun Φ hΦ => by
    simp only [Function.comp_apply]
    rw [← GlobalTheory.T.weil_gauss_constant_square F E χ hχ hχ1 σ Φ hΦ g hg]
    have e2 : ∫ z, Φ z * (γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z)) ∂muE E χ =
        γ * ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      ring
    rw [e2, ← GlobalTheory.T.weil_gauss_constant_norm_one F E χ hχ hχ1 η hcη hη Φ hΦ g hg g0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    by_cases ha : a = 0
    · subst ha
      simp [g0]
    · have := hγ (Units.mk0 a ha) Φ hΦ
      simp only [Units.val_mk0] at this
      rw [this]
      ring)
  have h1 := congrFun key (σ w)
  simp only [Function.comp_apply, AlgEquiv.symm_apply_apply] at h1
  rw [h1, Algebra.norm_eq_of_algEquiv]

/- English proof (translation)
Establish `he : quasiCharExponent μ = 0` using `by simp [quasiCharExponent, hμ.2]`. Establish `hs1 : -quasiCharExponent μ < ((1 / 2 : ℂ)).re` using `by rw [he]; norm_num`. Establish `hs2 : ((1 / 2 : ℂ)).re < 1 - quasiCharExponent μ` using `by rw [he]; norm_num`. Establish `hs' : -quasiCharExponent μ⁻¹ < ((1 : ℂ) - 1 / 2).re`. Rewrite using `[quasiCharExponent_inv, Complex.sub_re, Complex.one_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL1` using `localLFactor_ne_zero hμ.1 hs1`. Establish `hL2` using `localLFactor_ne_zero (continuous_quasiChar_inv hμ.1) hs'`. Establish `hfe` using `localZeta_functionalEquation hψ hψ1 hμ.1 hf hs1 hs2`. Establish `h12 : (1 : ℂ) - 1 / 2 = 1 / 2` using `by norm_num`.

Unfold `gam`. Rewrite `hfe`, `hL2`, the goal using `[h12]`. Clear denominators, using `at hfe ⊢` for the nonvanishing conditions. Take the linear combination `hfe`.
-/
theorem zeta_fe {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {μ : Kˣ →* ℂˣ} (hμ : IsUnit1 μ) {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) μ⁻¹ (1 / 2) = gam ψ μ (1 / 2) * localZeta f μ (1 / 2) := by
  have he : quasiCharExponent μ = 0 := by simp [quasiCharExponent, hμ.2]
  have hs1 : -quasiCharExponent μ < ((1 / 2 : ℂ)).re := by rw [he]; norm_num
  have hs2 : ((1 / 2 : ℂ)).re < 1 - quasiCharExponent μ := by rw [he]; norm_num
  have hs' : -quasiCharExponent μ⁻¹ < ((1 : ℂ) - 1 / 2).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hμ.1 hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hμ.1) hs'
  have hfe := localZeta_functionalEquation hψ hψ1 hμ.1 hf hs1 hs2
  have h12 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold gam
  rw [h12] at hfe hL2 ⊢
  field_simp at hfe ⊢
  linear_combination hfe

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_const, fun x => by simp⟩`.
-/
theorem isUnit1_one {K : Type} [Field K] [TopologicalSpace K] : IsUnit1 (1 : Kˣ →* ℂˣ) :=
  ⟨continuous_const, fun x => by simp⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη γ hγ`. Use `haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔ a ∈ (normUnits F E).range`. Use `fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨t, (coe_normUnits t).symm⟩`. Establish `hq : η = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E`.

Use extensionality with `a`. Rewrite using `[hη a]`. Unfold `Ad3.K.GL2LocalData.nsg`. Distinguish the cases in `ha : a ∈ (normUnits F E).range`. Rewrite using `[if_pos ((hex a).2 ha), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, Units.val_one]`.

Rewrite using `[if_neg (fun h => ha ((hex a).1 h)), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]`. Simplify using the standard rewrite rules. Establish `hcη : Continuous η`. Use `continuous_of_continuousAt_one η ?_` and prove the remaining obligations. Establish `hker : IsOpen (η.ker : Set Fˣ)`.

Rewrite using `[hq]`. Conclude with `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_ker_quadChar`. Establish `hev : (fun _ : Fˣ => (1 : ℂˣ)) =ᶠ[nhds 1] η` using `by filter_upwards [hker.mem_nhds (one_mem η.ker)] with x hx`. Conclude with `(MonoidHom.mem_ker.1 hx).symm`. Establish `h0 : ContinuousAt (fun _ : Fˣ => (1 : ℂˣ)) 1` using `continuousAt_const`.

Conclude with `h0.congr hev`. Establish `hu : IsUnit1 η` using `⟨hcη, fun a => by`. Rewrite using `[hη]`. Unfold `Ad3.K.GL2LocalData.nsg`. Apply the tactic sequence `split_ifs <;> simp⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Fˣ, η t = -1 := by`. Assume the negation of the conclusion as `hno`. Apply `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_ne_one (K := F) (E := E)` to reduce the goal to its premises. Use extensionality with `a`. Distinguish the cases in `ha : a ∈ (normUnits F E).range`.

Rewrite using `[GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha]`. Simplify using the standard rewrite rules. Conclude with `absurd ⟨a, by rw [hq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]⟩ hno`. Establish `hcE : Continuous (chE E χ)` using `GroundTheory.LocalField.continuous_traceChar hχ hχ1`. Establish `hnE : chE E χ ≠ 1` using `GroundTheory.LocalField.traceChar_ne_one hχ hχ1`.

Take `⟨κ, hκ, hfib⟩` from `GlobalTheory.CompanionTheory.NormFib.wFib F χ hχ hχ1 E hd hc σ hσ η hη`. Take `⟨g, hg, g0, hA, hB⟩` from `GlobalTheory.T.exists_schwartz_zeta_separating_character F η hcη t ht`. Take `⟨hgt, hZ⟩` from `GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0`. Establish `hf` using `localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg`. Establish `hft` using `localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt`.

Establish `hpt` using `ptw F E χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0`. Establish `hΨ` using `GlobalTheory.T.schwartz_norm_form_pullback F E _ hf`. Establish `hE` using `zeta_fe hcE hnE (isUnit1_one (K := E)) hΨ`. Rewrite `hE` using `[inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul]`. Establish `hfun : localFourier (selfDualMeasure (chE E χ)) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) = fun w => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)`.

Use function extensionality and compare the values at `w`. Rewrite using `[GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0]`. Conclude with `hpt w`. Rewrite `hE` using `[hfun]`. Establish `hscal : localZeta (fun w : E => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) = γ * localZeta (fun w : E => localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F …`.

Unfold `localZeta`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [mul_assoc]`. Rewrite `hE` using `[hscal, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hf, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hft]`.

Establish `e1` using `zeta_fe hχ hχ1 (isUnit1_one (K := F)) hg`. Establish `e2` using `zeta_fe hχ hχ1 hu hg`. Establish `e3` using `zeta_fe hχ hχ1 (isUnit1_one (K := F)) hgt`. Establish `e4` using `zeta_fe hχ hχ1 hu hgt`. Establish `hinv : η⁻¹ = η`.

Use extensionality with `a`. Establish `h2` using `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq (K := F) (E := E) a`. Rewrite `h2` using `[← hq]`. Establish `: (η a)⁻¹ = η a`. Rewrite using `[inv_eq_iff_mul_eq_one, ← sq, h2]`.

Simplify using `[this]`. Rewrite `e1`, `e3` using `[inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul]`. Rewrite `e2`, `e4` using `[hinv]`. Establish `z1` using `hZ 1`. Establish `z2` using `hZ η`.

Simplify using `only [inv_one, mul_one, mul_inv_cancel, map_one, MonoidHom.one_apply, Units.val_one, one_mul] at z1 z2`. Rewrite `hE` using `[e1, e2, e3, e4, z1, z2, hA]`. Establish `hκ' : ((κ : ℂ) / 2) ≠ 0`. Establish `: (κ : ℂ) ≠ 0` using `by exact_mod_cast hκ.ne'`. Conclude with `div_ne_zero this two_ne_zero`.

Unfold `lamE`. Rewrite using `[GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul, div_one]`. Establish `: ((κ : ℂ) / 2 * localZeta g η (1 / 2)) * (γ - gam χ η (1 / 2)) = 0`. Take the linear combination `hE`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `absurd h (mul_ne_zero hκ' hB)`. Conclude with `sub_eq_zero.1 h`.
-/
theorem wGaussLam : Ad3.K.GL2LocalData.WGaussLam := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη γ hγ
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔
      a ∈ (normUnits F E).range := by
    refine fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩
    rintro ⟨t, rfl⟩
    exact ⟨t, (coe_normUnits t).symm⟩
  have hq : η = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E := by
    ext a
    rw [hη a]
    unfold Ad3.K.GL2LocalData.nsg
    by_cases ha : a ∈ (normUnits F E).range
    · rw [if_pos ((hex a).2 ha), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, Units.val_one]
    · rw [if_neg (fun h => ha ((hex a).1 h)), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]
      simp
  have hcη : Continuous η := by
    refine continuous_of_continuousAt_one η ?_
    have hker : IsOpen (η.ker : Set Fˣ) := by
      rw [hq]
      exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_ker_quadChar
    have hev : (fun _ : Fˣ => (1 : ℂˣ)) =ᶠ[nhds 1] η := by
      filter_upwards [hker.mem_nhds (one_mem η.ker)] with x hx
      exact (MonoidHom.mem_ker.1 hx).symm
    have h0 : ContinuousAt (fun _ : Fˣ => (1 : ℂˣ)) 1 := continuousAt_const
    exact h0.congr hev
  have hu : IsUnit1 η := ⟨hcη, fun a => by
    rw [hη]
    unfold Ad3.K.GL2LocalData.nsg
    split_ifs <;> simp⟩
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, η t = -1 := by
    by_contra hno
    apply GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_ne_one (K := F) (E := E)
    ext a
    by_cases ha : a ∈ (normUnits F E).range
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha]; simp
    · exact absurd ⟨a, by rw [hq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]⟩ hno
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  obtain ⟨κ, hκ, hfib⟩ := GlobalTheory.CompanionTheory.NormFib.wFib F χ hχ hχ1 E hd hc σ hσ η hη
  obtain ⟨g, hg, g0, hA, hB⟩ := GlobalTheory.T.exists_schwartz_zeta_separating_character F η hcη t ht
  obtain ⟨hgt, hZ⟩ := GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hft := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt

  have hpt := ptw F E χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf

  have hE := zeta_fe hcE hnE (isUnit1_one (K := E)) hΨ
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at hE
  have hfun : localFourier (selfDualMeasure (chE E χ)) (chE E χ)
      (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) =
      fun w => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w) := by
    funext w
    rw [GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0]
    exact hpt w
  rw [hfun] at hE
  have hscal : localZeta (fun w : E => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) =
      γ * localZeta (fun w : E => localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) := by
    unfold localZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [mul_assoc]
  rw [hscal, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hf, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hft] at hE
  have e1 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hg
  have e2 := zeta_fe hχ hχ1 hu hg
  have e3 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hgt
  have e4 := zeta_fe hχ hχ1 hu hgt
  have hinv : η⁻¹ = η := by
    ext a
    have h2 := GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq (K := F) (E := E) a
    rw [← hq] at h2
    have : (η a)⁻¹ = η a := by
      rw [inv_eq_iff_mul_eq_one, ← sq, h2]
    simp [this]
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at e1 e3
  rw [hinv] at e2 e4
  have z1 := hZ 1
  have z2 := hZ η
  simp only [inv_one, mul_one, mul_inv_cancel, map_one, MonoidHom.one_apply, Units.val_one, one_mul] at z1 z2
  rw [e1, e2, e3, e4, z1, z2, hA] at hE
  have hκ' : ((κ : ℂ) / 2) ≠ 0 := by
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    exact div_ne_zero this two_ne_zero
  unfold lamE
  rw [GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul, div_one]
  have : ((κ : ℂ) / 2 * localZeta g η (1 / 2)) * (γ - gam χ η (1 / 2)) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero hκ' hB)
  · exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.GaussLam
