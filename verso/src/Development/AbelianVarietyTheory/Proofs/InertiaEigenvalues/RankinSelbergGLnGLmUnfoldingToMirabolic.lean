import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralMulConjNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageMulInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialCoeffGoodOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerPartialCoeffBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLLastRowAndDetModuleUnderLeftMultiplicatiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VerticalStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalDomainPoissonCuspidal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmUnfold
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

/- English proof (translation)
Introduce `E _ _ _ m r μ _`. Use `⟨1, one_pos, ?_⟩` and prove the remaining obligations. Introduce `π π' hπ hπ' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x h1 h2`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)`.

Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)`. Take `⟨oc, hoc, hπoc⟩` from `hπ`. Take `⟨oc', hoc', hπoc'⟩` from `hπ'`. Rewrite `hπoc`, `hπoc'` using `[CuspSub.hasCentral_iff]`. Take `⟨hc, hl, hv⟩` from `GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E (m + r + 1) π oc hoc hπoc φ hφ`.

Take `⟨hc', hl', hv'⟩` from `GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' oc' hoc' hπoc' φ' hφ'`. Establish `hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C` using `(GlobalTheory.JSWPosR.mspanR_le_bddForms hoc hπoc hφ).2.2.2`. Establish `hmk : m + 1 ≤ m + r + 1` using `by omega`. Take `⟨hR1, hR2, hR3, hR4, hR5⟩` from `GlobalTheory.T.adelicGLLastRow_and_detModule_under_left_multiplication E m`. Take `⟨Fh, hFh⟩ : ∃ Fh, Fh = GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F` from `⟨_, rfl⟩`.

Establish `hFhc : Continuous Fh` using `hFh ▸ GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi (GroundTheory.Automorphic.GJMatrix.adelicFourierPi_mem_schwartzBruhatPi hF)`. Establish `hlrc : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g` using `continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last m) j`. Establish `hdc : ∀ a : ℝ, Continuous fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ a` using `fun a => GlobalTheory.RSnm.continuous_detAbs.rpow_const fun g => Or.inl (GlobalTheory.RSnm.detAbs_pos g).ne'`. Establish `hdγ : ∀ (γ : GL (Fin (m + 1)) E) g, GlobalTheory.RSnm.detAbs (ratGL E (m + 1) γ * g) = GlobalTheory.RSnm.detAbs g`. Introduce `γ g`.

Establish `: GlobalTheory.RSnm.detAbs (ratGL E (m + 1) γ) = 1`. Simplify using `[GlobalTheory.RSnm.detAbs, GlobalTheory.ShortVecDecay.ideleModule_det_rat]`. Rewrite using `[GlobalTheory.RSnm.detAbs_mul, this, one_mul]`. Establish `hrγ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) = GlobalTheory.ZEul.lastRow g`. Introduce `γ hγ g`.

Rewrite using `[hR1, hR3 γ hγ, ← hR2]`. Take `⟨sq, hsq⟩ : ∃ sq : ℂ → ℂ, sq = fun z => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `hsqc : Continuous sq` using `hsq ▸ GlobalTheory.T.continuous_mul_norm_rpow_neg_half'`. Establish `hsqn : ∀ z, ‖sq z‖ = Real.sqrt ‖z‖`. Introduce `z`.

Rewrite using `[hsq]`. Distinguish the cases in `hz : z = 0`. Simplify using `[hz]`. Establish `ht : 0 < ‖z‖` using `norm_pos_iff.2 hz`. Simplify using `only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_one_add' ht.le (by norm_num)]`. Evaluate the numerical expressions. Establish `hsqm : ∀ z, sq z * ((Real.sqrt ‖z‖ : ℝ) : ℂ) = z`. Introduce `z`. Rewrite using `[hsq]`.

Distinguish the cases in `hz : z = 0`. Simplify using `[hz]`. Establish `ht : 0 < ‖z‖` using `norm_pos_iff.2 hz`. Rewrite using `[mul_assoc, ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_add ht]`. Evaluate the numerical expressions.

Take `⟨Q, hQ⟩ : ∃ Q : GA E (m + 1) → ℂ, Q = fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)` from `⟨_, rfl⟩`. Establish `hGQ : Good (GlobalTheory.StdCharConductor.psi E) m Q` using `hQ ▸ GlobalTheory.T.partial_coeff_good_of_cuspidal E (m + r + 1) m hmk φ hc hl hv`. Take `⟨c1, hc1⟩ : ∃ c1 : GA E (m + 1) → ℂ, c1 = fun g => sq (Fh (GlobalTheory.ZEul.lastRow g)) * ((GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ)` from `⟨_, rfl⟩`. Take `⟨c2, hc2⟩ : ∃ c2 : GA E (m + 1) → ℂ, c2 = fun g => ((Real.sqrt ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x / 2) : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `hc1c : Continuous c1`.

Rewrite using `[hc1]`. Conclude with `(hsqc.comp (hFhc.comp hlrc)).mul (Complex.continuous_ofReal.comp (hdc _))`. Establish `hc2c : Continuous c2`. Rewrite using `[hc2]`. Conclude with `Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp (continuous_norm.comp (hFhc.comp hlrc))).mul (hdc _))`.

Establish `hc1γ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, c1 (ratGL E (m + 1) γ * g) = c1 g`. Introduce `γ hγ g`. Rewrite using `[hc1]`. Simplify using `only [hrγ γ hγ g, hdγ]`. Establish `hc2γ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, c2 (ratGL E (m + 1) γ * g) = c2 g`.

Introduce `γ hγ g`. Rewrite using `[hc2]`. Simplify using `only [hrγ γ hγ g, hdγ]`. Establish `hc1b : ∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), c1 (blkU y * g) = c1 g`. Introduce `r l y g`.

Rewrite using `[hc1]`. Simplify using `only [(hR4 r l y g).1, (hR4 r l y g).2]`. Establish `hc2b : ∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), c2 (blkU y * g) = c2 g`. Introduce `r l y g`. Rewrite using `[hc2]`.

Simplify using `only [(hR4 r l y g).1, (hR4 r l y g).2]`. Establish `hc1u : ∀ X g, c1 (uGL X * g) = c1 g`. Introduce `X g`. Rewrite using `[hc1]`. Simplify using `only [GlobalTheory.ZUnf.lastRow_uGL_mul, hR5]`.

Establish `hc2u : ∀ X g, c2 (uGL X * g) = c2 g`. Introduce `X g`. Rewrite using `[hc2]`. Simplify using `only [GlobalTheory.ZUnf.lastRow_uGL_mul, hR5]`. Take `⟨f1, hf1⟩ : ∃ f1 : GA E (m + 1) → ℂ, f1 = fun g => c1 g * Q g` from `⟨_, rfl⟩`.

Take `⟨f2, hf2⟩ : ∃ f2 : GA E (m + 1) → ℂ, f2 = fun g => c2 g * φ' g` from `⟨_, rfl⟩`. Establish `hG1 : Good (GlobalTheory.StdCharConductor.psi E) m f1` using `hf1 ▸ GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous E (m + 1) m _ Q c1 hGQ hc1c hc1γ hc1b`. Establish `hG2 : Good (GlobalTheory.StdCharConductor.psi E) m f2` using `hf2 ▸ GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous E (m + 1) m _ φ' c2 (GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages E m _ φ' hc' hl' hv') hc2c hc2γ hc2b`. Establish `whit_mul : ∀ (c f : GA E (m + 1) → ℂ), (∀ X g, c (uGL X * g) = c g) → ∀ g, GlobalTheory.JSW.whit (fun g => c g * f g) g = c g * GlobalTheory.JSW.whit f g`. Introduce `c f hcu g`.

Simplify using `only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]`. Rewrite using `[← MeasureTheory.integral_const_mul]`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hcu]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hWg : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g` using `fun f hf g => GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (GlobalTheory.ZUnf.isMir_of_mem_mirU_zero hγ) g) g`. Establish `hW1 : ∀ g, GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g = c1 g * GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)`. Introduce `g`. Rewrite using `[← hWg f1 hG1 g, hf1, whit_mul c1 Q hc1u g, hQ, GlobalTheory.T.whittaker_partial_coeff_block E (m + r + 1) m hmk φ hc g]`.

Establish `hW2 : ∀ g, GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g = c2 g * GlobalTheory.JSW.whit φ' g`. Introduce `g`. Rewrite using `[← hWg f2 hG2 g, hf2, whit_mul c2 φ' hc2u g]`. Establish `hdpos : ∀ g : GA E (m + 1), 0 < GlobalTheory.RSnm.detAbs g` using `GlobalTheory.RSnm.detAbs_pos`. Establish `hc1n : ∀ g, ‖c1 g‖ ^ 2 = ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1))`.

Introduce `g`. Rewrite using `[hc1]`. Simplify using `only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hdpos g).le _), hsqn, mul_pow, Real.sq_sqrt (norm_nonneg _)]`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (hdpos g).le]`. Evaluate the numerical expressions.

Establish `hc2n : ∀ g, ‖c2 g‖ ^ 2 = ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x`. Introduce `g`. Rewrite using `[hc2]`. Simplify using `only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hdpos g).le _)), mul_pow, Real.sq_sqrt (norm_nonneg _)]`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (hdpos g).le]`.

Evaluate the numerical expressions. Establish `hen : ∀ (c W : ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B → ‖c‖ ^ 2 = A * B → ‖c * W‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = ‖W‖ₑ ^ 2 * ENNReal.ofReal A * ENNReal.ofReal B`. Introduce `c W A B hA hB h`. Rewrite using `[ENNReal.coe_one, mul_one, enorm_mul, mul_pow, ← ofReal_norm_eq_enorm c, ← ENNReal.ofReal_pow (norm_nonneg _), h, ENNReal.ofReal_mul hA]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ` from `by haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)`. Conclude with `GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ`. Establish `h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ` using `GlobalTheory.ZUnf.NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀`. Establish `hU` using `GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E) 𝓕P 𝓕₀ h𝓕P h𝓕₀' (fun _ => (1 : NNReal)) measurable_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)`. Establish `hd1 : ∫⁻ g in 𝓕P, ‖f1 g‖ₑ ^ 2 * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ≥0∞) ∂μ ≠ ⊤`.

Rewrite using `[hU.1 _ hG1]`. Use `ne_of_eq_of_ne (lintegral_congr fun g => ?_) h1` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = _`. Rewrite using `[hW1, hen _ _ _ _ (norm_nonneg _) (Real.rpow_nonneg (hdpos g).le _) (hc1n g), ofReal_norm_eq_enorm, hFh]`. Establish `hd2 : ∫⁻ g in 𝓕P, ‖f2 g‖ₑ ^ 2 * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ≥0∞) ∂μ ≠ ⊤`.

Rewrite using `[hU.1 _ hG2]`. Use `ne_of_eq_of_ne (lintegral_congr fun g => ?_) h2` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = _`. Rewrite using `[hW2, hen _ _ _ _ (norm_nonneg _) (Real.rpow_nonneg (hdpos g).le _) (hc2n g), ofReal_norm_eq_enorm, hFh]`. Take `⟨hI1, hI2, hEq⟩` from `hU.2 f1 f2 hG1 hG2 hd1 hd2`.

Establish `hD : ∀ g : GA E (m + 1), ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2) = ((GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((GlobalTheory.RSnm.detAbs g ^ (x / 2) : ℝ) : ℂ)`. Introduce `g`. Rewrite using `[← Complex.ofReal_mul, ← Real.rpow_add (hdpos g), Complex.ofReal_cpow (hdpos g).le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpair : ∀ (z P W : ℂ) (d : ℝ), 0 < d → (sq z * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ)) * P * conj (((Real.sqrt ‖z‖ * d ^ (x / 2) : ℝ) : ℂ) * W) = P * conj W * z * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((d ^ (x / 2) : ℝ) : ℂ)`. Introduce `z P W d _`. Rewrite using `[map_mul, Complex.conj_ofReal, Complex.ofReal_mul]`. Take the linear combination `(P * conj W * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((d ^ (x / 2) : ℝ) : ℂ)) * hsqm z`.

Establish `hfun : (fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) (m + 1 - 1) f1 g * conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) (m + 1 - 1) f2 g) * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ)) = GlobalTheory.RSnmUnf.uIntNM (by omeg …`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g * conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g) * (((1 : NNReal) : ℝ) : ℂ) = _`. Rewrite using `[hW1, hW2, hc1, hc2, GlobalTheory.RSnmUnf.uIntNM, hD, NNReal.coe_one, Complex.ofReal_one, mul_one]`. Simplify using `only`.

Rewrite using `[hpair _ _ _ _ (hdpos g), hFh]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv0 : (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) ≠ 0` using `fun h0 => by simpa using congrFun h0 (Fin.last m)`. Establish `hP : ∀ γ : GL (Fin (m + 1)) E, γ ∈ mirU E (m + 1) m ↔ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1` using `fun γ => by`. Rewrite using `[mem_mirU_last, Matrix.single_one_vecMul, funext_iff]`.

Simplify using `only [Pi.single_apply, Matrix.row]`. Take `⟨γ, e, hγ, he⟩` from `GlobalTheory.ThetaUnfold.exists_transversal hv0 hP`. Use `haveI := GlobalTheory.ThetaUnfold.countable_range_ratGL (E := E) (a := m + 1)`. Take `⟨H, hH⟩ : ∃ H : GA E (m + 1) → ℂ, H = fun g => f1 g * conj (f2 g) * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ)` from `⟨_, rfl⟩`. Establish `hHinv : ∀ δ ∈ (mirU E (m + 1) m).map (ratGL E (m + 1)), ∀ g, H (δ * g) = H g`.

Introduce and unpack `_ ⟨γ', hγ', rfl⟩ g`. Establish `hm : IsMir m γ'`. Introduce `i k h`. Establish `hk` using `k.2`. Establish `hi` using `i.2`.

Apply the tactic sequence `have hi' : m ≤ (i : ℕ) := by rcases h with h | h <;> omega`. Conclude with `hγ' i k hi' (by rw [Fin.le_def]; omega)`. Rewrite using `[hH]`. Simplify using `only [hG1.left γ' hm g, hG2.left γ' hm g]`. Establish `hHm : AEStronglyMeasurable H μ`.

Rewrite using `[hH]`. Conclude with `((hG1.cont.mul (Complex.continuous_conj.comp hG2.cont)).mul continuous_const).aestronglyMeasurable`. Establish `hfin : ∫⁻ g in 𝓕, ∑' ξ, ‖H (ratGL E (m + 1) (γ ξ) * g)‖ₑ ∂μ ≠ ⊤`. Rewrite using `[GlobalTheory.ThetaUnfold.lintegral_unfold μ _ _ (fun ξ => ratGL E (m + 1) (γ ξ)) e he h𝓕 h𝓕P (fun g => ‖H g‖ₑ) (fun δ hδ g => by simp only [hHinv δ hδ g]) hHm.enorm]`. Rewrite using `[hH]`.

Conclude with `hI1.2.ne`. Take `⟨-, -, -, hEqU⟩` from `GlobalTheory.ThetaUnfold.integral_unfold μ _ _ (fun ξ => ratGL E (m + 1) (γ ξ)) e he h𝓕 h𝓕P H hHinv hHm hfin`. Establish `hpt : ∀ g, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) g = ∑' ξ, H (ratGL E (m + 1) (γ ξ) * g)`. Introduce `g`. Establish `hs` using `GlobalTheory.T.fundamental_domain_poisson_cuspidal E (m + r + 1) m hmk φ hc hb hl hv F hF γ hγ g`.

Rewrite using `[GlobalTheory.RSnm.rsIntegrand, ← hs.tsum_eq, ← tsum_mul_right, ← tsum_mul_right]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[hH, hD]`. Simplify using `only [hf1, hf2, hc1, hc2, NNReal.coe_one, Complex.ofReal_one, mul_one, hR1, hγ, hdγ, hl', hQ]`. Rewrite using `[hpair _ _ _ _ (hdpos g), hFh]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfun]`. Conclude with `hI2`. Rewrite using `[Complex.ofReal_one, one_mul, ← hfun, ← hEq]`.

Use `(MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_` and prove the remaining obligations. Rewrite using `[hEqU, hH]`.
-/
theorem rs_unfold : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧ ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ), φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)), ∀ 𝓕 𝓕₀ : Set (GA E (m + 1)),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤ → ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) 𝓕₀ μ ∧
      ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) h ∂μ =
        (c : ℂ) * ∫ h in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x h ∂μ := by
  intro E _ _ _ m r μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' hπ hπ' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x h1 h2
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨oc, hoc, hπoc⟩ := hπ
  obtain ⟨oc', hoc', hπoc'⟩ := hπ'
  rw [CuspSub.hasCentral_iff] at hπoc hπoc'
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E (m + r + 1) π oc hoc hπoc φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' oc' hoc' hπoc' φ' hφ'
  have hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := (GlobalTheory.JSWPosR.mspanR_le_bddForms hoc hπoc hφ).2.2.2
  have hmk : m + 1 ≤ m + r + 1 := by omega
  obtain ⟨hR1, hR2, hR3, hR4, hR5⟩ := GlobalTheory.T.adelicGLLastRow_and_detModule_under_left_multiplication E m
  obtain ⟨Fh, hFh⟩ : ∃ Fh, Fh = GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F := ⟨_, rfl⟩
  have hFhc : Continuous Fh := hFh ▸ GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi
    (GroundTheory.Automorphic.GJMatrix.adelicFourierPi_mem_schwartzBruhatPi hF)
  have hlrc : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g :=
    continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last m) j
  have hdc : ∀ a : ℝ, Continuous fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ a := fun a =>
    GlobalTheory.RSnm.continuous_detAbs.rpow_const fun g => Or.inl (GlobalTheory.RSnm.detAbs_pos g).ne'
  have hdγ : ∀ (γ : GL (Fin (m + 1)) E) g, GlobalTheory.RSnm.detAbs (ratGL E (m + 1) γ * g) = GlobalTheory.RSnm.detAbs g := by
    intro γ g
    have : GlobalTheory.RSnm.detAbs (ratGL E (m + 1) γ) = 1 := by
      simp [GlobalTheory.RSnm.detAbs, GlobalTheory.ShortVecDecay.ideleModule_det_rat]
    rw [GlobalTheory.RSnm.detAbs_mul, this, one_mul]
  have hrγ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) = GlobalTheory.ZEul.lastRow g := by
    intro γ hγ g
    rw [hR1, hR3 γ hγ, ← hR2]

  obtain ⟨sq, hsq⟩ : ∃ sq : ℂ → ℂ, sq = fun z => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hsqc : Continuous sq := hsq ▸ GlobalTheory.T.continuous_mul_norm_rpow_neg_half'
  have hsqn : ∀ z, ‖sq z‖ = Real.sqrt ‖z‖ := by
    intro z
    rw [hsq]
    by_cases hz : z = 0
    · simp [hz]
    have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' ht.le (by norm_num)]
    norm_num
  have hsqm : ∀ z, sq z * ((Real.sqrt ‖z‖ : ℝ) : ℂ) = z := by
    intro z
    rw [hsq]
    by_cases hz : z = 0
    · simp [hz]
    have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [mul_assoc, ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    norm_num
  obtain ⟨Q, hQ⟩ : ∃ Q : GA E (m + 1) → ℂ, Q = fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) :=
    ⟨_, rfl⟩
  have hGQ : Good (GlobalTheory.StdCharConductor.psi E) m Q := hQ ▸ GlobalTheory.T.partial_coeff_good_of_cuspidal E (m + r + 1) m hmk φ hc hl hv
  obtain ⟨c1, hc1⟩ : ∃ c1 : GA E (m + 1) → ℂ, c1 = fun g => sq (Fh (GlobalTheory.ZEul.lastRow g)) *
      ((GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2 : GA E (m + 1) → ℂ, c2 = fun g =>
      ((Real.sqrt ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc1c : Continuous c1 := by
    rw [hc1]
    exact (hsqc.comp (hFhc.comp hlrc)).mul (Complex.continuous_ofReal.comp (hdc _))
  have hc2c : Continuous c2 := by
    rw [hc2]
    exact Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp (continuous_norm.comp (hFhc.comp hlrc))).mul (hdc _))
  have hc1γ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, c1 (ratGL E (m + 1) γ * g) = c1 g := by
    intro γ hγ g; rw [hc1]; simp only [hrγ γ hγ g, hdγ]
  have hc2γ : ∀ γ : GL (Fin (m + 1)) E, IsMir m γ → ∀ g, c2 (ratGL E (m + 1) γ * g) = c2 g := by
    intro γ hγ g; rw [hc2]; simp only [hrγ γ hγ g, hdγ]
  have hc1b : ∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), c1 (blkU y * g) = c1 g := by
    intro r l y g; rw [hc1]; simp only [(hR4 r l y g).1, (hR4 r l y g).2]
  have hc2b : ∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), c2 (blkU y * g) = c2 g := by
    intro r l y g; rw [hc2]; simp only [(hR4 r l y g).1, (hR4 r l y g).2]
  have hc1u : ∀ X g, c1 (uGL X * g) = c1 g := by
    intro X g; rw [hc1]; simp only [GlobalTheory.ZUnf.lastRow_uGL_mul, hR5]
  have hc2u : ∀ X g, c2 (uGL X * g) = c2 g := by
    intro X g; rw [hc2]; simp only [GlobalTheory.ZUnf.lastRow_uGL_mul, hR5]
  obtain ⟨f1, hf1⟩ : ∃ f1 : GA E (m + 1) → ℂ, f1 = fun g => c1 g * Q g := ⟨_, rfl⟩
  obtain ⟨f2, hf2⟩ : ∃ f2 : GA E (m + 1) → ℂ, f2 = fun g => c2 g * φ' g := ⟨_, rfl⟩
  have hG1 : Good (GlobalTheory.StdCharConductor.psi E) m f1 := hf1 ▸ GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous E (m + 1) m _ Q c1 hGQ hc1c hc1γ hc1b
  have hG2 : Good (GlobalTheory.StdCharConductor.psi E) m f2 :=
    hf2 ▸ GlobalTheory.T.isMirabolicWhittakerStage_mul_invariant_continuous E (m + 1) m _ φ' c2 (GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages E m _ φ' hc' hl' hv') hc2c hc2γ hc2b
  have whit_mul : ∀ (c f : GA E (m + 1) → ℂ), (∀ X g, c (uGL X * g) = c g) → ∀ g,
      GlobalTheory.JSW.whit (fun g => c g * f g) g = c g * GlobalTheory.JSW.whit f g := by
    intro c f hcu g
    simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only
    rw [hcu]
    ring
  have hWg : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (GlobalTheory.ZUnf.isMir_of_mem_mirU_zero hγ) g) g
  have hW1 : ∀ g, GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g =
      c1 g * GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g) := by
    intro g
    rw [← hWg f1 hG1 g, hf1, whit_mul c1 Q hc1u g, hQ, GlobalTheory.T.whittaker_partial_coeff_block E (m + r + 1) m hmk φ hc g]
  have hW2 : ∀ g, GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g = c2 g * GlobalTheory.JSW.whit φ' g := by
    intro g
    rw [← hWg f2 hG2 g, hf2, whit_mul c2 φ' hc2u g]

  have hdpos : ∀ g : GA E (m + 1), 0 < GlobalTheory.RSnm.detAbs g := GlobalTheory.RSnm.detAbs_pos
  have hc1n : ∀ g, ‖c1 g‖ ^ 2 = ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) := by
    intro g
    rw [hc1]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hdpos g).le _), hsqn,
      mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hdpos g).le]
    norm_num
  have hc2n : ∀ g, ‖c2 g‖ ^ 2 = ‖Fh (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x := by
    intro g
    rw [hc2]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hdpos g).le _)),
      mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hdpos g).le]
    norm_num
  have hen : ∀ (c W : ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B → ‖c‖ ^ 2 = A * B →
      ‖c * W‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = ‖W‖ₑ ^ 2 * ENNReal.ofReal A * ENNReal.ofReal B := by
    intro c W A B hA hB h
    rw [ENNReal.coe_one, mul_one, enorm_mul, mul_pow, ← ofReal_norm_eq_enorm c, ← ENNReal.ofReal_pow (norm_nonneg _), h,
      ENNReal.ofReal_mul hA]
    ring
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := GlobalTheory.ZUnf.NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (fun _ => (1 : NNReal)) measurable_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hd1 : ∫⁻ g in 𝓕P, ‖f1 g‖ₑ ^ 2 * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG1]
    refine ne_of_eq_of_ne (lintegral_congr fun g => ?_) h1
    change ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = _
    rw [hW1, hen _ _ _ _ (norm_nonneg _) (Real.rpow_nonneg (hdpos g).le _) (hc1n g), ofReal_norm_eq_enorm, hFh]
  have hd2 : ∫⁻ g in 𝓕P, ‖f2 g‖ₑ ^ 2 * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG2]
    refine ne_of_eq_of_ne (lintegral_congr fun g => ?_) h2
    change ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g‖ₑ ^ 2 * ((1 : NNReal) : ℝ≥0∞) = _
    rw [hW2, hen _ _ _ _ (norm_nonneg _) (Real.rpow_nonneg (hdpos g).le _) (hc2n g), ofReal_norm_eq_enorm, hFh]
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 f1 f2 hG1 hG2 hd1 hd2

  have hD : ∀ g : GA E (m + 1), ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2) =
      ((GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((GlobalTheory.RSnm.detAbs g ^ (x / 2) : ℝ) : ℂ) := by
    intro g
    rw [← Complex.ofReal_mul, ← Real.rpow_add (hdpos g), Complex.ofReal_cpow (hdpos g).le]
    congr 1
    push_cast
    ring
  have hpair : ∀ (z P W : ℂ) (d : ℝ), 0 < d →
      (sq z * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ)) * P * conj (((Real.sqrt ‖z‖ * d ^ (x / 2) : ℝ) : ℂ) * W) =
        P * conj W * z * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((d ^ (x / 2) : ℝ) : ℂ) := by
    intro z P W d _
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    linear_combination (P * conj W * ((d ^ ((x - ((r : ℝ) + 1)) / 2) : ℝ) : ℂ) * ((d ^ (x / 2) : ℝ) : ℂ)) * hsqm z
  have hfun : (fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) (m + 1 - 1) f1 g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) (m + 1 - 1) f2 g) * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ)) =
      GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x := by
    funext g
    change GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f1 g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f2 g) * (((1 : NNReal) : ℝ) : ℂ) = _
    rw [hW1, hW2, hc1, hc2, GlobalTheory.RSnmUnf.uIntNM, hD, NNReal.coe_one, Complex.ofReal_one, mul_one]
    simp only
    rw [hpair _ _ _ _ (hdpos g), hFh]
    ring

  have hv0 : (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) ≠ 0 := fun h0 => by simpa using congrFun h0 (Fin.last m)
  have hP : ∀ γ : GL (Fin (m + 1)) E, γ ∈ mirU E (m + 1) m ↔
      Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1 := fun γ => by
    rw [mem_mirU_last, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
  obtain ⟨γ, e, hγ, he⟩ := GlobalTheory.ThetaUnfold.exists_transversal hv0 hP
  haveI := GlobalTheory.ThetaUnfold.countable_range_ratGL (E := E) (a := m + 1)
  obtain ⟨H, hH⟩ : ∃ H : GA E (m + 1) → ℂ, H = fun g => f1 g * conj (f2 g) * (((fun _ => (1 : NNReal)) g : NNReal) : ℝ) :=
    ⟨_, rfl⟩
  have hHinv : ∀ δ ∈ (mirU E (m + 1) m).map (ratGL E (m + 1)), ∀ g, H (δ * g) = H g := by
    rintro _ ⟨γ', hγ', rfl⟩ g
    have hm : IsMir m γ' := by
      intro i k h
      have hk := k.2
      have hi := i.2
      have hi' : m ≤ (i : ℕ) := by rcases h with h | h <;> omega
      exact hγ' i k hi' (by rw [Fin.le_def]; omega)
    rw [hH]
    simp only [hG1.left γ' hm g, hG2.left γ' hm g]
  have hHm : AEStronglyMeasurable H μ := by
    rw [hH]
    exact ((hG1.cont.mul (Complex.continuous_conj.comp hG2.cont)).mul continuous_const).aestronglyMeasurable
  have hfin : ∫⁻ g in 𝓕, ∑' ξ, ‖H (ratGL E (m + 1) (γ ξ) * g)‖ₑ ∂μ ≠ ⊤ := by
    rw [GlobalTheory.ThetaUnfold.lintegral_unfold μ _ _ (fun ξ => ratGL E (m + 1) (γ ξ)) e he h𝓕 h𝓕P (fun g => ‖H g‖ₑ)
      (fun δ hδ g => by simp only [hHinv δ hδ g]) hHm.enorm]
    rw [hH]
    exact hI1.2.ne
  obtain ⟨-, -, -, hEqU⟩ := GlobalTheory.ThetaUnfold.integral_unfold μ _ _ (fun ξ => ratGL E (m + 1) (γ ξ)) e he h𝓕 h𝓕P H hHinv hHm hfin
  have hpt : ∀ g, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) g =
      ∑' ξ, H (ratGL E (m + 1) (γ ξ) * g) := by
    intro g
    have hs := GlobalTheory.T.fundamental_domain_poisson_cuspidal E (m + r + 1) m hmk φ hc hb hl hv F hF γ hγ g
    rw [GlobalTheory.RSnm.rsIntegrand, ← hs.tsum_eq, ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    rw [hH, hD]
    simp only [hf1, hf2, hc1, hc2, NNReal.coe_one, Complex.ofReal_one, mul_one, hR1, hγ, hdγ, hl', hQ]
    rw [hpair _ _ _ _ (hdpos g), hFh]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hfun]
    exact hI2
  · rw [Complex.ofReal_one, one_mul, ← hfun, ← hEq]
    refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
    rw [hEqU, hH]

end GlobalTheory.RSnmUnfold
