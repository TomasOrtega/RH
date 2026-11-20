import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDensityOnEqFibreIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresLocalHermitianFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTopStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfLintegralSmoothEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousHasCompactSupportInfFinProductTestFuncStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanLEqOfRealMeanCReStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.OneVecMeas

/- English proof (translation)
Introduce `hOV F E _ _ _ _ _ σ hCM M J hJ hM β hβ d b Φ Φi Φf Φv hΦi hpure hreal hΦ`. Establish `hOV'` using `hOV F E σ hCM M J hJ`. Establish `H0` using `hOV'.2 hM β hβ d b (fun _ => 0) (fun _ => 0) Φf Φv continuous_const HasCompactSupport.zero (fun N e _ _ => contDiff_const) hpure (fun X => by simp)`. Use `⟨H0.1, fun ψ hψ => ?_⟩` and prove the remaining obligations. Establish `H1` using `H0.2 ψ hψ`.

Use `⟨H1.1, fun μ hμ => ⟨(H1.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩⟩` and prove the remaining obligations. Establish `H2` using `(H1.2 μ hμ).2 𝓕 h𝓕`. Establish `hfin : μ 𝓕 < ⊤` using `(hOV'.1.2 μ hμ).2 𝓕 h𝓕`. Use `⟨H2.1, H2.2.1, H2.2.2.1, H2.2.2.2.1, ?_⟩` and prove the remaining obligations. Introduce `μi νi μv νv hμi hνi hμv hνv`.

Establish `hCc` using `fun (Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) h1 h2 h3 h5 => ((((hOV'.2 hM β hβ d b Φ' Φi' Φf Φv h1 h2 h3 hpure h5).2 ψ hψ).2 μ hμ).2 𝓕 h𝓕).2.2.2.2 μi νi μv νv hμi hνi hμv hνv`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hCM M J μi νi (by omega) hJ hμi.1 hνi.1`. Conclude with `⟨fun v => Classical.choose (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1), fun v => Classical.choose_spec (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) …`. Introduce `fi fv hfi hfv`.

Establish `: IsTotallyReal F` using `hCM.1`. Establish `: Countable E` using `(Module.finBasis ℚ E).equivFun.toEquiv.injective.countable`. Use `set βi : Ainf F := algebraMap F (Ainf F) β with hβi`. Establish `hβiB : βi ∈ {c : Ainf F | ∀ w, c w ≠ 0}` using `(FibExist.isUnit_ainf_iff βi).1 ((Ne.isUnit hβ).map (algebraMap F (Ainf F)))`. Establish `hβv : ∀ v, algebraMap F (Fv F v) β ≠ 0` using `fun v => (map_ne_zero _).2 hβ`.

Establish `hBi : {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0}` using `Set.ext fun c => FibExist.isUnit_ainf_iff c`. Establish `hBio : IsOpen {c : Ainf F | ∀ w, c w ≠ 0}`. Establish `: {c : Ainf F | ∀ w, c w ≠ 0} = ⋂ w, {c : Ainf F | c w ≠ 0}` using `by ext; simp`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_ne.preimage (continuous_apply w)`.

Establish `hΦvR : ∀ v, Φv v = fun X => (((Φv v X).re : ℝ) : ℂ)` using `fun v => funext fun X => Complex.ext (by simp) (by simp [(hreal v X).2])`. Establish `hΦfR : ∀ Y, Φf Y = (((Φf Y).re : ℝ) : ℂ) ∧ 0 ≤ (Φf Y).re`. Introduce `Y`. Establish `e1 : Φf Y = ((∏ᶠ v, (Φv v (projV v Y)).re : ℝ) : ℂ)`. Establish `h1` using `Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective (fun v => (Φv v (projV v Y)).re)`.

Rewrite using `[hpure.2.2 Y]`. Conclude with `(finprod_congr fun v => congrFun (hΦvR v) _).trans h1.symm`. Rewrite using `[e1]`. Conclude with `⟨by simp, by simpa using finprod_nonneg fun v => (hreal v _).1⟩`. Establish `hdensV : ∀ (Fl : ∀ v, Fv F v → ℂ), (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) → ∀ v, Fl v (algebraMap F (Fv F v) β) = ((∫ X, (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) : ℝ) : ℂ) ∧ ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v ( …`.

Introduce `Fl hFl v`. Use `(hνv v).1` as an intermediate fact. Establish `h' : IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (fun X => (((Φv v X).re : ℝ) : ℂ)) (Fl v)`. Rewrite using `[← hΦvR v]`. Conclude with `hFl v`.

Conclude with `GlobalTheory.T.contDensity_eq_fibre_integral _ _ (μv v) _ (νv v) _ (fv v) (fun X => (Φv v X).re) (Fl v) (FibExist.continuous_qR (Fv F v) σ J) isOpen_ne (hfv v) (Complex.continuous_re.comp (hpure.1 v).1.continuous) ((hpure.1 v).2.comp_left Complex.zero_re) (fun X => (hreal v X).1) …`. Take `⟨Fi0, Fl0, -, hFl0, hmul0, -⟩` from `hCc (fun _ => 0) (fun _ => 0) continuous_const HasCompactSupport.zero (fun N e _ _ => contDiff_const) (fun X => by simp)`. Establish `hFlR : ∀ (Fl : ∀ v, Fv F v → ℂ), (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) → Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) → Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) …`. Introduce `Fl hFl hm`. Establish `e : (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) = fun v => ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re` using `funext fun v => (hdensV Fl hFl v).2`.

Rewrite using `[e]`. Conclude with `GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real _ _ hm fun v => by`. Rewrite using `[(hdensV Fl hFl v).1]`. Conclude with `⟨by simp, by simpa using integral_nonneg fun X => (hreal v X).1⟩`. Use `⟨(hFlR Fl0 hFl0 hmul0).1, ?_⟩` and prove the remaining obligations.

Use `set C := ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) with hC`. Establish `hCtop : C < ⊤` using `by rw [(hFlR Fl0 hFl0 hmul0).2]; exact ENNReal.ofReal_lt_top`. Take `⟨k, eK, hK⟩` from `PI.VolStabS.exists_coord_tens F E`. Take `⟨k1, e1, h1⟩` from `PI.VolStabS.exists_coord_pi eK hK (Fin M)`. Take `⟨N, eV, hV⟩` from `PI.VolStabS.exists_coord_pi e1 h1 (Fin 1)`.

Set `eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)` to `{ eV.toEquiv with map_add' := hV }`. Establish `hsmooth : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (N' : ℕ) (e' : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N' → ℝ)), Continuous e' → Continuous e'.symm → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm)`. Introduce `φ hφ N' e' _ he'`. Set `L` to `((eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) →+ (Fin N → ℝ)).comp (e'.symm : (Fin N' → ℝ) →+ (Fin 1 → Fin M → Ainf F ⊗[F] E))).toRealLinearMap (eV.continuous.comp he')`. Establish `: ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) = Complex.ofRealCLM ∘ φ ∘ L` using `rfl`.

Rewrite using `[this]`. Conclude with `Complex.ofRealCLM.contDiff.comp (hφ.comp L.contDiff)`. Set `act : (Fin 1 → Fin M → E) → HA (AF F) σ J → (Fin 1 → Fin M → AF F ⊗[F] E)` to `fun x h => h⁻¹ • ratTup (F := F) (AF F) x`. Establish `hact : ∀ x, Continuous (act x)` using `fun x => continuous_inv.smul continuous_const`. Establish `hpF : Continuous (projFin (F` using `F) (E := E) (M := M) (n := 1)) := continuous_pi fun a => continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp ((continuous_apply i).comp (continuous_apply a))`.

Establish `hpI : Continuous (projInf (F` using `F) (E := E) (M := M) (n := 1)) := GlobalTheory.GaugeGlue.continuous_projInf b`. Establish `hΦfc` using `GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact F E d M 1 b Φf Φv hpure`. Set `T : Set (Fin 1 → Fin M → E)` to `{x | hE σ J (x 0) (x 0) = algebraMap F E β}`. Establish `hS : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β} = T`. Use extensionality with `x`.

Use `⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩` and prove the remaining obligations. Establish `: hE σ J (x 0) (x 0) = 0` using `by rw [h0]; simp [hE, Formalism.UG.hform]`. Conclude with `(map_ne_zero (algebraMap F E)).2 hβ (h.symm.trans this)`. Set `a : T → HA (AF F) σ J → (Fin N → ℝ)` to `fun x h => eV (projInf (act x h))`. Set `w : T → HA (AF F) σ J → ℝ≥0∞` to `fun x h => ENNReal.ofReal (Φf (projFin (act x h))).re`.

Establish `ha : ∀ x, Continuous (a x)` using `fun x => eV.continuous.comp (hpI.comp (hact x))`. Establish `hwr : ∀ x, Continuous fun h => (Φf (projFin (act x h))).re` using `fun x => Complex.continuous_re.comp (hΦfc.1.comp (hpF.comp (hact x)))`. Establish `hw : ∀ x, Continuous (w x)` using `fun x => ENNReal.continuous_ofReal.comp (hwr x)`. Set `m₁ : Measure (Fin N → ℝ)` to `(μ 𝓕)⁻¹ • Measure.sum fun x : T => ((μ.restrict 𝓕).withDensity (w x)).map (a x)`. Establish `hm₁ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂m₁ = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, g (a x h) * w x h ∂μ`.

Introduce `g hg`. Establish `hts` using `lintegral_tsum (μ := μ.restrict 𝓕) (f := fun (x : T) h => g (a x h) * w x h) fun x => ((hg.comp (ha x).measurable).mul (hw x).measurable).aemeasurable`. Use `beta_reduce at hts`. Rewrite using `[lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul, hts]`. Use `congr 1`.

Use `tsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hg (ha x).measurable]`. Establish `hwd` using `lintegral_withDensity_eq_lintegral_mul (μ.restrict 𝓕) (hw x).measurable (hg.comp (ha x).measurable)`. Simplify using `only [Function.comp_def] at hwd`. Rewrite using `[hwd]`.

Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Set `m₂ : Measure (Fin N → ℝ)` to `C • (fi βi).map eV`. Establish `hm₂ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂m₂ = C * ∫⁻ X, g (eV X) ∂(fi βi)`.

Introduce `g hg`. Rewrite using `[lintegral_smul_measure, lintegral_map hg eV.continuous.measurable, smul_eq_mul]`. Establish `hfoc : IsFiniteMeasureOnCompacts m₂`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨f, hf1, -, hfcs, -⟩` from `exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)`.

Establish `hint` using `(hfi.2.2 (fun X => f (eV X)) (f.continuous.comp eV.continuous) (hfcs.comp_homeomorph eV) (Set.subset_univ _)).1 βi hβiB`. Establish `hle : (fi βi) (eV ⁻¹' K) ≤ ∫⁻ X, ‖f (eV X)‖ₑ ∂(fi βi)`. Rewrite using `[← lintegral_indicator_one (hK.isClosed.measurableSet.preimage eV.continuous.measurable)]`. Use `lintegral_mono fun X => ?_` and prove the remaining obligations. Distinguish the cases in `hX : X ∈ eV ⁻¹' K`.

Rewrite using `[Set.indicator_of_mem hX, Pi.one_apply, hf1 hX, Pi.one_apply]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hX]`. Conclude with `bot_le`. Use `show (C • (fi βi).map eV) K < ⊤`.

Rewrite using `[Measure.smul_apply, Measure.map_apply eV.continuous.measurable hK.isClosed.measurableSet, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top hCtop (hle.trans_lt hint.2)`. Establish `htest : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → (∀ y, 0 ≤ φ y) → ∫⁻ y, ENNReal.ofReal (φ y) ∂m₁ = ∫⁻ y, ENNReal.ofReal (φ y) ∂m₂`. Introduce `φ hφ hφcs hφ0`. Establish `hφc : Continuous φ` using `hφ.continuous`.

Set `Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ` to `fun X => ((φ (eV X) : ℝ) : ℂ)`. Set `Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ` to `fun X => Φi' (projInf X) * Φf (projFin X)`. Establish `hΦi'c : Continuous Φi'` using `Complex.continuous_ofReal.comp (hφc.comp eV.continuous)`. Establish `hΦi'cs : HasCompactSupport Φi'` using `(hφcs.comp_homeomorph eV).comp_left Complex.ofReal_zero`. Establish `hΦ'c` using `GlobalTheory.T.continuous_hasCompactSupport_infFin_product_testFunction F E M 1 Φ' Φi' Φf hΦi'c hΦi'cs hΦfc.1 hΦfc.2 (fun X => rfl)`.

Take `⟨Fi', Fl', hdi, hdv, hmul', hmean'⟩` from `hCc Φ' Φi' hΦi'c hΦi'cs (hsmooth φ hφ) (fun X => rfl)`. Rewrite `hdi` using `[hBi]`. Use `hνi.1` as an intermediate fact. Establish `hFi` using `GlobalTheory.T.contDensity_eq_fibre_integral _ _ μi _ νi _ fi (fun X => φ (eV X)) Fi' (FibExist.continuous_qR (Ainf F) σ J) hBio hfi (hφc.comp eV.continuous) (hφcs.comp_homeomorph eV) (fun X => hφ0 _) hdi βi hβiB`. Establish `hP` using `hFlR Fl' hdv hmul'`.

Set `f : T → HA (AF F) σ J → ℝ` to `fun x h => φ (a x h) * (Φf (projFin (act x h))).re`. Establish `hf0 : ∀ x h, 0 ≤ f x h` using `fun x h => mul_nonneg (hφ0 _) (hΦfR _).2`. Establish `hfm : ∀ x, Measurable (f x)` using `fun x => ((hφc.comp (ha x)).mul (hwr x)).measurable`. Establish `hΦ'f : ∀ (x : T) h, Φ' (act x h) = ((f x h : ℝ) : ℂ)`. Introduce `x h`.

Use `show ((φ (eV (projInf (act x h))) : ℝ) : ℂ) * Φf (projFin (act x h)) = ((φ (eV (projInf (act x h))) * (Φf (projFin (act x h))).re : ℝ) : ℂ)`. Use `conv_lhs => rw [(hΦfR (projFin (act x h))).1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hint` using `GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top F E σ hCM M J hJ β hβ Φ' hΦ'c.1 hΦ'c.2 μ 𝓕 hμ h𝓕`.

Establish `hint' : ∫⁻ h in 𝓕, ∑' x : T, ‖((f x h : ℝ) : ℂ)‖ₑ ∂μ < ⊤`. Use `lt_of_eq_of_lt ?_ hint` and prove the remaining obligations. Use `lintegral_congr fun h => tsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← hΦ'f]`. Establish `hL` using `GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC (HA (AF F) σ J) μ 𝓕 T f hfm hf0 hfin hint'`.

Rewrite using `[hm₁ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable), hm₂ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable)]`. Establish `e1 : (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, ENNReal.ofReal (φ (a x h)) * w x h ∂μ = meanL μ 𝓕 (fun h => ∑' x : T, ENNReal.ofReal (f x h))`. Unfold `meanL`. Use `congr 1`. Use `lintegral_congr fun h => tsum_congr fun x => ?_` and prove the remaining obligations.

Simplify using `only [f, w]`. Rewrite using `[ENNReal.ofReal_mul (hφ0 _)]`. Rewrite using `[e1, hL]`. Establish `e2 : meanC μ 𝓕 (fun h => ∑' x : T, ((f x h : ℝ) : ℂ)) = Fi' βi * ∏' v, Fl' v (algebraMap F (Fv F v) β)`. Rewrite using `[← hmean']`.

Unfold `thSum`. Use `congr 1`. Use function extensionality and compare the values at `h`. Conclude with `tsum_congr fun x => (hΦ'f x h).symm`. Rewrite using `[e2, hP.2, hFi.2, hFi.1]`.

Establish `hr : 0 ≤ ∫ X, φ (eV X) ∂(fi βi)` using `integral_nonneg fun X => hφ0 _`. Simplify using `only [Complex.re_ofReal_mul, Complex.ofReal_re]`. Rewrite using `[ENNReal.ofReal_mul hr, mul_comm]`. Use `hfoc` as an intermediate fact. Establish `hm : m₁ = m₂` using `GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' N m₁ m₂ htest`.

Rewrite using `[hS]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hm₁ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable)]`. Unfold `meanL`. Use `congr 1`.

Use `lintegral_congr fun h => tsum_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [a, w, act, hΦ, Homeomorph.symm_apply_apply]`. Use `_ = ∫⁻ y, Φi (eV.symm y) ∂m₂ := by rw [hm]`. Use `_ = (∫⁻ X, Φi X ∂(fi βi)) * C := by`. Rewrite using `[hm₂ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable), mul_comm]`.

Simplify using `only [Homeomorph.symm_apply_apply]`.
-/
theorem sw1b2_of_cc : GlobalTheory.GaussMean.OneVectorCc → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SW1b2 F E σ M J := by
  intro hOV F E _ _ _ _ _ σ hCM M J hJ hM β hβ d b Φ Φi Φf Φv hΦi hpure hreal hΦ
  have hOV' := hOV F E σ hCM M J hJ
  have H0 := hOV'.2 hM β hβ d b (fun _ => 0) (fun _ => 0) Φf Φv continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) hpure (fun X => by simp)
  refine ⟨H0.1, fun ψ hψ => ?_⟩
  have H1 := H0.2 ψ hψ
  refine ⟨H1.1, fun μ hμ => ⟨(H1.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩⟩
  have H2 := (H1.2 μ hμ).2 𝓕 h𝓕
  have hfin : μ 𝓕 < ⊤ := (hOV'.1.2 μ hμ).2 𝓕 h𝓕
  refine ⟨H2.1, H2.2.1, H2.2.2.1, H2.2.2.2.1, ?_⟩
  intro μi νi μv νv hμi hνi hμv hνv
  have hCc := fun (Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) h1 h2 h3 h5 =>
    ((((hOV'.2 hM β hβ d b Φ' Φi' Φf Φv h1 h2 h3 hpure h5).2 ψ hψ).2 μ hμ).2 𝓕 h𝓕).2.2.2.2 μi νi μv νv hμi hνi hμv hνv
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hCM M J μi νi (by omega) hJ hμi.1 hνi.1
  · exact ⟨fun v => Classical.choose (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1),
      fun v => Classical.choose_spec (GlobalTheory.T.exists_fibreMeasures_localHermitianForm F E σ hCM M J hJ (by omega) v (μv v) (νv v) (hμv v).1 (hνv v).1)⟩
  intro fi fv hfi hfv

  have : IsTotallyReal F := hCM.1
  have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  set βi : Ainf F := algebraMap F (Ainf F) β with hβi
  have hβiB : βi ∈ {c : Ainf F | ∀ w, c w ≠ 0} :=
    (FibExist.isUnit_ainf_iff βi).1 ((Ne.isUnit hβ).map (algebraMap F (Ainf F)))
  have hβv : ∀ v, algebraMap F (Fv F v) β ≠ 0 := fun v => (map_ne_zero _).2 hβ
  have hBi : {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} :=
    Set.ext fun c => FibExist.isUnit_ainf_iff c
  have hBio : IsOpen {c : Ainf F | ∀ w, c w ≠ 0} := by
    have : {c : Ainf F | ∀ w, c w ≠ 0} = ⋂ w, {c : Ainf F | c w ≠ 0} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_ne.preimage (continuous_apply w)
  have hΦvR : ∀ v, Φv v = fun X => (((Φv v X).re : ℝ) : ℂ) := fun v => funext fun X =>
    Complex.ext (by simp) (by simp [(hreal v X).2])
  have hΦfR : ∀ Y, Φf Y = (((Φf Y).re : ℝ) : ℂ) ∧ 0 ≤ (Φf Y).re := by
    intro Y
    have e1 : Φf Y = ((∏ᶠ v, (Φv v (projV v Y)).re : ℝ) : ℂ) := by
      have h1 := Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective
        (fun v => (Φv v (projV v Y)).re)
      rw [hpure.2.2 Y]
      exact (finprod_congr fun v => congrFun (hΦvR v) _).trans h1.symm
    rw [e1]
    exact ⟨by simp, by simpa using finprod_nonneg fun v => (hreal v _).1⟩

  have hdensV : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      ∀ v, Fl v (algebraMap F (Fv F v) β) =
          ((∫ X, (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) : ℝ) : ℂ) ∧
        ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
          ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl v
    have := (hνv v).1
    have h' : IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0}
        (fun X => (((Φv v X).re : ℝ) : ℂ)) (Fl v) := by
      rw [← hΦvR v]; exact hFl v
    exact GlobalTheory.T.contDensity_eq_fibre_integral _ _ (μv v) _ (νv v) _ (fv v) (fun X => (Φv v X).re) (Fl v)
      (FibExist.continuous_qR (Fv F v) σ J) isOpen_ne (hfv v)
      (Complex.continuous_re.comp (hpure.1 v).1.continuous) ((hpure.1 v).2.comp_left Complex.zero_re)
      (fun X => (hreal v X).1) h' _ (hβv v)

  obtain ⟨Fi0, Fl0, -, hFl0, hmul0, -⟩ := hCc (fun _ => 0) (fun _ => 0) continuous_const HasCompactSupport.zero
    (fun N e _ _ => contDiff_const) (fun X => by simp)
  have hFlR : ∀ (Fl : ∀ v, Fv F v → ℂ),
      (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) →
      Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) →
      Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) ∧
      ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) =
        ENNReal.ofReal (∏' v, Fl v (algebraMap F (Fv F v) β)).re := by
    intro Fl hFl hm
    have e : (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) =
        fun v => ENNReal.ofReal (Fl v (algebraMap F (Fv F v) β)).re := funext fun v => (hdensV Fl hFl v).2
    rw [e]
    exact GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real _ _ hm fun v => by
      rw [(hdensV Fl hFl v).1]
      exact ⟨by simp, by simpa using integral_nonneg fun X => (hreal v X).1⟩
  refine ⟨(hFlR Fl0 hFl0 hmul0).1, ?_⟩
  set C := ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β)) with hC
  have hCtop : C < ⊤ := by rw [(hFlR Fl0 hFl0 hmul0).2]; exact ENNReal.ofReal_lt_top

  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin 1)
  let eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  have hsmooth : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (N' : ℕ) (e' : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N' → ℝ)), Continuous e' → Continuous e'.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) := by
    intro φ hφ N' e' _ he'
    let L := ((eA : (Fin 1 → Fin M → Ainf F ⊗[F] E) →+ (Fin N → ℝ)).comp
      (e'.symm : (Fin N' → ℝ) →+ (Fin 1 → Fin M → Ainf F ⊗[F] E))).toRealLinearMap
      (eV.continuous.comp he')
    have : ((fun X => ((φ (eV X) : ℝ) : ℂ)) ∘ e'.symm) = Complex.ofRealCLM ∘ φ ∘ L := rfl
    rw [this]
    exact Complex.ofRealCLM.contDiff.comp (hφ.comp L.contDiff)

  let act : (Fin 1 → Fin M → E) → HA (AF F) σ J → (Fin 1 → Fin M → AF F ⊗[F] E) :=
    fun x h => h⁻¹ • ratTup (F := F) (AF F) x
  have hact : ∀ x, Continuous (act x) := fun x => continuous_inv.smul continuous_const
  have hpF : Continuous (projFin (F := F) (E := E) (M := M) (n := 1)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpI : Continuous (projInf (F := F) (E := E) (M := M) (n := 1)) := GlobalTheory.GaugeGlue.continuous_projInf b
  have hΦfc := GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact F E d M 1 b Φf Φv hpure
  let T : Set (Fin 1 → Fin M → E) := {x | hE σ J (x 0) (x 0) = algebraMap F E β}
  have hS : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β} = T := by
    ext x
    refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
    have : hE σ J (x 0) (x 0) = 0 := by rw [h0]; simp [hE, Formalism.UG.hform]
    exact (map_ne_zero (algebraMap F E)).2 hβ (h.symm.trans this)
  let a : T → HA (AF F) σ J → (Fin N → ℝ) := fun x h => eV (projInf (act x h))
  let w : T → HA (AF F) σ J → ℝ≥0∞ := fun x h => ENNReal.ofReal (Φf (projFin (act x h))).re
  have ha : ∀ x, Continuous (a x) := fun x => eV.continuous.comp (hpI.comp (hact x))
  have hwr : ∀ x, Continuous fun h => (Φf (projFin (act x h))).re :=
    fun x => Complex.continuous_re.comp (hΦfc.1.comp (hpF.comp (hact x)))
  have hw : ∀ x, Continuous (w x) := fun x => ENNReal.continuous_ofReal.comp (hwr x)
  let m₁ : Measure (Fin N → ℝ) := (μ 𝓕)⁻¹ • Measure.sum fun x : T => ((μ.restrict 𝓕).withDensity (w x)).map (a x)
  have hm₁ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₁ = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, g (a x h) * w x h ∂μ := by
    intro g hg
    have hts := lintegral_tsum (μ := μ.restrict 𝓕) (f := fun (x : T) h => g (a x h) * w x h)
      fun x => ((hg.comp (ha x).measurable).mul (hw x).measurable).aemeasurable
    beta_reduce at hts
    rw [lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul, hts]
    congr 1
    refine tsum_congr fun x => ?_
    rw [lintegral_map hg (ha x).measurable]
    have hwd := lintegral_withDensity_eq_lintegral_mul (μ.restrict 𝓕) (hw x).measurable (hg.comp (ha x).measurable)
    simp only [Function.comp_def] at hwd
    rw [hwd]
    refine lintegral_congr fun h => ?_
    simp only [Pi.mul_apply]
    ring
  let m₂ : Measure (Fin N → ℝ) := C • (fi βi).map eV
  have hm₂ : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂m₂ = C * ∫⁻ X, g (eV X) ∂(fi βi) := by
    intro g hg
    rw [lintegral_smul_measure, lintegral_map hg eV.continuous.measurable, smul_eq_mul]

  have hfoc : IsFiniteMeasureOnCompacts m₂ := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨f, hf1, -, hfcs, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
    have hint := (hfi.2.2 (fun X => f (eV X)) (f.continuous.comp eV.continuous) (hfcs.comp_homeomorph eV)
      (Set.subset_univ _)).1 βi hβiB
    have hle : (fi βi) (eV ⁻¹' K) ≤ ∫⁻ X, ‖f (eV X)‖ₑ ∂(fi βi) := by
      rw [← lintegral_indicator_one (hK.isClosed.measurableSet.preimage eV.continuous.measurable)]
      refine lintegral_mono fun X => ?_
      by_cases hX : X ∈ eV ⁻¹' K
      · rw [Set.indicator_of_mem hX, Pi.one_apply, hf1 hX, Pi.one_apply]; simp
      · rw [Set.indicator_of_notMem hX]; exact bot_le
    show (C • (fi βi).map eV) K < ⊤
    rw [Measure.smul_apply, Measure.map_apply eV.continuous.measurable hK.isClosed.measurableSet, smul_eq_mul]
    exact ENNReal.mul_lt_top hCtop (hle.trans_lt hint.2)

  have htest : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∀ y, 0 ≤ φ y) → ∫⁻ y, ENNReal.ofReal (φ y) ∂m₁ = ∫⁻ y, ENNReal.ofReal (φ y) ∂m₂ := by
    intro φ hφ hφcs hφ0
    have hφc : Continuous φ := hφ.continuous
    let Φi' : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ := fun X => ((φ (eV X) : ℝ) : ℂ)
    let Φ' : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φi' (projInf X) * Φf (projFin X)
    have hΦi'c : Continuous Φi' := Complex.continuous_ofReal.comp (hφc.comp eV.continuous)
    have hΦi'cs : HasCompactSupport Φi' := (hφcs.comp_homeomorph eV).comp_left Complex.ofReal_zero
    have hΦ'c := GlobalTheory.T.continuous_hasCompactSupport_infFin_product_testFunction F E M 1 Φ' Φi' Φf hΦi'c hΦi'cs hΦfc.1 hΦfc.2 (fun X => rfl)
    obtain ⟨Fi', Fl', hdi, hdv, hmul', hmean'⟩ := hCc Φ' Φi' hΦi'c hΦi'cs (hsmooth φ hφ) (fun X => rfl)
    rw [hBi] at hdi
    have := hνi.1
    have hFi := GlobalTheory.T.contDensity_eq_fibre_integral _ _ μi _ νi _ fi (fun X => φ (eV X)) Fi' (FibExist.continuous_qR (Ainf F) σ J)
      hBio hfi (hφc.comp eV.continuous) (hφcs.comp_homeomorph eV) (fun X => hφ0 _) hdi βi hβiB
    have hP := hFlR Fl' hdv hmul'
    let f : T → HA (AF F) σ J → ℝ := fun x h => φ (a x h) * (Φf (projFin (act x h))).re
    have hf0 : ∀ x h, 0 ≤ f x h := fun x h => mul_nonneg (hφ0 _) (hΦfR _).2
    have hfm : ∀ x, Measurable (f x) := fun x => ((hφc.comp (ha x)).mul (hwr x)).measurable
    have hΦ'f : ∀ (x : T) h, Φ' (act x h) = ((f x h : ℝ) : ℂ) := by
      intro x h
      show ((φ (eV (projInf (act x h))) : ℝ) : ℂ) * Φf (projFin (act x h)) =
        ((φ (eV (projInf (act x h))) * (Φf (projFin (act x h))).re : ℝ) : ℂ)
      conv_lhs => rw [(hΦfR (projFin (act x h))).1]
      push_cast; ring
    have hint := GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top F E σ hCM M J hJ β hβ Φ' hΦ'c.1 hΦ'c.2 μ 𝓕 hμ h𝓕
    have hint' : ∫⁻ h in 𝓕, ∑' x : T, ‖((f x h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ := by
      refine lt_of_eq_of_lt ?_ hint
      refine lintegral_congr fun h => tsum_congr fun x => ?_
      rw [← hΦ'f]
    have hL := GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC (HA (AF F) σ J) μ 𝓕 T f hfm hf0 hfin hint'
    rw [hm₁ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable),
      hm₂ (fun y => ENNReal.ofReal (φ y)) (ENNReal.measurable_ofReal.comp hφc.measurable)]
    have e1 : (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' x : T, ENNReal.ofReal (φ (a x h)) * w x h ∂μ =
        meanL μ 𝓕 (fun h => ∑' x : T, ENNReal.ofReal (f x h)) := by
      unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
      simp only [f, w]; rw [ENNReal.ofReal_mul (hφ0 _)]
    rw [e1, hL]
    have e2 : meanC μ 𝓕 (fun h => ∑' x : T, ((f x h : ℝ) : ℂ)) =
        Fi' βi * ∏' v, Fl' v (algebraMap F (Fv F v) β) := by
      rw [← hmean']; unfold thSum; congr 1; funext h; exact tsum_congr fun x => (hΦ'f x h).symm
    rw [e2, hP.2, hFi.2, hFi.1]
    have hr : 0 ≤ ∫ X, φ (eV X) ∂(fi βi) := integral_nonneg fun X => hφ0 _
    simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [ENNReal.ofReal_mul hr, mul_comm]
  have := hfoc
  have hm : m₁ = m₂ := GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' N m₁ m₂ htest
  rw [hS]
  calc meanL μ 𝓕 (fun h => ∑' x : T, Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E)))
      = ∫⁻ y, Φi (eV.symm y) ∂m₁ := by
        rw [hm₁ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable)]
        unfold meanL; congr 1; refine lintegral_congr fun h => tsum_congr fun x => ?_
        simp only [a, w, act, hΦ, Homeomorph.symm_apply_apply]
    _ = ∫⁻ y, Φi (eV.symm y) ∂m₂ := by rw [hm]
    _ = (∫⁻ X, Φi X ∂(fi βi)) * C := by
        rw [hm₂ (fun y => Φi (eV.symm y)) (hΦi.comp eV.symm.continuous.measurable), mul_comm]
        simp only [Homeomorph.symm_apply_apply]

end GlobalTheory.OneVecMeas
