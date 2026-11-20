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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFourierGaussLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValLastRowEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumPadTermNeTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonnegStatement
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmCells

/- English proof (translation)
Establish `h1 : (GlobalTheory.RSnmUnf.padNat (n` using `n) fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by`. Use function extensionality and compare the values at `i`. Simplify using `[GlobalTheory.RSnmUnf.padNat]`. Establish `h2 : (fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0` using `by funext i; simp`. Rewrite using `[GlobalTheory.RSnmUnf.rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, h1, h2]`.

Simplify using `[GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]`.
-/
theorem rsTermNM_zero (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) :
    GlobalTheory.RSnmUnf.rsTermNM q α β x 0 = 1 := by
  have h1 : (GlobalTheory.RSnmUnf.padNat (n := n) fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by
    funext i; simp [GlobalTheory.RSnmUnf.padNat]
  have h2 : (fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by funext i; simp
  rw [GlobalTheory.RSnmUnf.rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, h1, h2]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

/- English proof (translation)
Introduce `E _ _ _ m r S hψ π π' hπ hπ' α β φ φ' κ hφ hφ' hU hK hU' hK' hshβ hshα hmatch hκc hκ0 hκN hκC hκU h₀`. Establish `hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E)`. Introduce `w`. Take `⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ` from `⟨_, Formalism.L2.Host.unif_spec w⟩`. Use `⟨Units.mk0 ϖ fun h => ?_, hϖ⟩` and prove the remaining obligations.

Rewrite `hϖ` using `[IsUnifV, h]`. Simplify using `at hϖ`. Use `choose ϖ hϖ using hϖex`. Establish `hreg : ∀ {a : ℕ} {ρ : CuspSub E a}, ρ.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR ρ, GlobalTheory.JSW.IsBCC F`. Introduce `a ρ hρ F hF`.

Take `⟨ψ, rfl, h⟩` from `GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hρ F hF`. Establish `h0` using `(h []).2`. Rewrite `h0` using `[GlobalTheory.JSW.word_nil]`. Then use the resulting hypothesis. Establish `hc` using `hreg hπ φ hφ`. Establish `hc'` using `hreg hπ' φ' hφ'`.

Establish `hW : ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g` using `fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g`. Establish `hW' : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g` using `fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g`. Establish `hWc` using `GlobalTheory.JSW.WhitCont.continuous_whit E _ φ hc.cont hc.bdd`. Establish `hWc'` using `GlobalTheory.JSW.WhitCont.continuous_whit E _ φ' hc'.cont hc'.bdd`. Establish `hRI : ∀ {a : ℕ} (Φ : GA E a → ℂ), (∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, Φ (g * finGL E a u) = Φ g) → (∀ w ∉ S, ∀ k ∈ KGL w a, ∀ g, Φ (g * finGL E a (locGL E a w k)) = Φ g) → ∀ k : GL (Fin a) (Af E), (∀ v, Matrix.GeneralLinearGro …`.

Introduce `a Φ ⟨U, hUo, hUi⟩ hKi k hk1 hk2 g`. Set `stab : Subgroup (GL (Fin a) (Af E))` to `{ carrier := {k | ∀ g, Φ (g * finGL E a k) = Φ g} mul_mem' := fun {a' c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha] one_mem' := fun g => by rw [map_one, mul_one] inv_mem' := fun {a'} ha g => by`. Rewrite using `[← ha (g * finGL E a a'⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }`. Set `V : Subgroup (GL (Fin a) (Af E))` to `U ⊔ Subgroup.closure {k | ∃ w ∉ S, ∃ k' ∈ KGL w a, locGL E a w k' = k}`. Establish `hVle : V ≤ stab`.

Use `sup_le (fun k hk => hUi k hk) (Subgroup.closure_le _ |>.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, k, hk, rfl⟩`. Conclude with `hKi w hw k hk`. Establish `hVo : IsOpen (V : Set (GL (Fin a) (Af E)))` using `Subgroup.isOpen_mono (le_sup_left : U ≤ V) hUo`. Establish `hVK : ∀ w ∉ S, ∀ k ∈ KGL w a, locGL E a w k ∈ V` using `fun w hw k hk => (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)`.

Take `⟨J, -, -, hJV⟩` from `GlobalTheory.RSLocalPart.exists_levelAt_subset S V hVo hVK`. Establish `hkJ : k ∈ GlobalTheory.RSLocalPart.levelAt a S J`. Use `⟨hk1, fun v hv i j => ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg (fun M : GL (Fin a) (v.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hk2 v hv)`. Establish `e2 : ((k.val - 1) i j) v = 0`.

Establish `e1' : pLoc E v (k.val i j) = (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j` using `by simpa using e1`. Express the relevant statement in the definitionally equal form `pLoc E v (k.val i j - (1 : Matrix (Fin a) (Fin a) (Af E)) i j) = 0`. Rewrite using `[map_sub, e1', Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e2, map_zero]`.

Conclude with `zero_le'`. Establish `e : (fun z => Φ (z * finGL E a k)) = Φ` using `funext fun z => hVle (hJV hkJ) z`. Rewrite using `[GlobalTheory.JSW.whit_mul_right, e]`. Establish `hWK` using `hRI φ hU hK`. Establish `hWK'` using `hRI φ' hU' hK'`.

Take `⟨h₀, hh₀, hκ₀, hW₀⟩` from `h₀`. Establish `hint : ∀ w ∉ S, ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) ∈ w.adicCompletionIntegers E`. Introduce `w hw j`. Establish `e1` using `congrArg (fun M : GL (Fin (m + 1)) (w.adicCompletion E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) (hh₀ w hw)`. Establish `e2 : pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j`.

Simplify `e1` using `[GlobalTheory.ZEul.lastRow]`. Rewrite using `[e2, Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Take `⟨F, hFSB, hFc, hFr, hFpos, hFsc⟩` from `GlobalTheory.FourierCell.exists_fourier_gauss_lattice E m S (GlobalTheory.ZEul.lastRow h₀) hint`. Use `⟨F, hFSB, ?_⟩` and prove the remaining obligations. Introduce `μ _ 𝓕₀ h𝓕`. Take `⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet, hDA, hDB⟩` from `GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg E m r S φ φ' κ F hWc hWc' hW hW' hWK hWK' hmatch hκc hκ0 hκC ⟨h₀, hh₀, hκ₀, hW₀, hFpos⟩ hFc hFr μ 𝓕₀ h𝓕`. Use `⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩` and prove the remaining obligations.

Introduce `x hx hdα hdβ`. Establish `ev` using `GlobalTheory.CellEvalNM.uIntNM_cell_eval E m r S hψ ϖ hϖ α β φ φ' F hW hW' hWK hWK' (hshβ ϖ hϖ) (hshα ϖ hϖ) (fun a ha y hy => hFsc ϖ hϖ a ha y hy) x`. Take `⟨hWbc, hFlc, hmeas, hinv, hbd⟩` from `GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hW hW' hFc`. Establish `hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S)` using `(GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet`. Use `set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI`.

Establish `hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I`. Rewrite using `[hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S`. Rewrite using `[Set.indicator_of_mem hg]`.

Rewrite using `[Set.indicator_of_notMem hg]`. Simplify using `[hfC g hg]`. Establish `hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ` using `h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet`. Establish `hlinD : ∀ (D : GA E (m + 1) → ℝ≥0∞) (c : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℝ≥0∞), Measurable D → (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, D (u * g) = D g) → (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * D …`. Introduce `D c hDm hDi hDc hD hc`.

Rewrite using `[GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 D hDm hDi]`. Establish `: ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = c l * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ`. Introduce `l`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Rewrite using `[← lintegral_const_mul'' _ hDm.aemeasurable]`.

Conclude with `lintegral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => hDc g hg.2 l)`. Repeatedly rewrite using `[this, ENNReal.tsum_mul_right]`. Conclude with `ENNReal.mul_ne_top hc hD`. Establish `hen : ∀ {a b : ℂ}, ‖a‖ = ‖b‖ → ‖a‖ₑ = ‖b‖ₑ` using `fun h => by`. Rewrite using `[← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]`.

Establish `hmD : ∀ s : ℝ, Measurable fun g : GA E (m + 1) => ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (Glo …` using `fun s => ((hWbc.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))`. Establish `hmD' : ∀ s : ℝ, Measurable fun g : GA E (m + 1) => ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)` using `fun s => ((hWc'.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))`. Establish `LA` using `hlinD _ _ (hmD _) (fun u hu g => by`. Take `⟨h1, -, h3, h4, -⟩` from `hinv u hu g`. Rewrite using `[hen h1, h3, h4]) (fun g hg l => (ev g hg l).2.1) (hDA x)`.

Use the proof step `(GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + r + 1 + 1) S (by omega) (fun w i => (α w i : ℂ)) x hdα)`. Establish `LB` using `hlinD _ _ (hmD' _) (fun u hu g => by`. Take `⟨-, h2, h3, h4, -⟩` from `hinv u hu g`. Rewrite using `[hen h2, h3, h4]) (fun g hg l => (ev g hg l).2.2) (hDB π' hπ' hφ' hFSB x hx)`. Use the proof step `(GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + 1) S le_rfl (fun w i => (β w i : ℂ)) x hdβ)`.

Use `⟨LA, LB, ?_⟩` and prove the remaining obligations. Establish `hDtr : ∀ (a b : ℂ) (s : ℝ) (g : GA E (m + 1)), (‖a‖ₑ ^ 2 * ‖b‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)).toReal = ‖a‖ ^ 2 * ‖b‖ * GlobalTheory.RSnm.detAbs g ^ s`. Introduce `a b s g`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm, ENNReal.toReal_ofReal (Real.rpow_nonneg (GlobalTheory.RSnm.detAbs_pos g).le _)]`. Establish `iA` using `integrable_toReal_of_lintegral_ne_top (hmD (x - ((r : ℝ) + 1))).aemeasurable LA`.

Establish `iB` using `integrable_toReal_of_lintegral_ne_top (hmD' x).aemeasurable LB`. Establish `i12 : Integrable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) (μ.restrict 𝓕₀)` using `Integrable.mono' ((iA.add iB).div_const 2) (hmeas x).aestronglyMeasurable (Filter.Eventually.of_forall fun g => by`. Simplify using `only [Pi.add_apply, hDtr]`. Conclude with `hbd x g)`. Establish `hl : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = (l.1.prod …`.

Introduce `l`. Rewrite using `[← integral_const_mul, ← hIC, ← integral_const_mul]`. Use `integral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[(ev g hg.2 l).1, hfu g hg.2, hdet, mul_assoc]`.

Establish `h` using `(GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 _ (hmeas x) i12 (fun u hu g => (hinv u hu g).2.2.2.2 x)).2`. Rewrite `h` using `[hl]`. Rewrite using `[← h.tsum_eq, tsum_mul_right, mul_comm]`. Take `⟨e, he⟩` from `GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)`. Use `congr 1`.

Rewrite using `[← e.tsum_eq]`. Conclude with `tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (β w i : ℂ)) x v) (fun i => rsTermNM_zero _ _ _ _) l).symm`.
-/
theorem unfolded_cells_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + r + 1 + 1), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  intro E _ _ _ m r S hψ π π' hπ hπ' α β φ φ' κ hφ hφ' hU hK hU' hK' hshβ hshα hmatch hκc hκ0 hκN hκC hκU h₀
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {a : ℕ} {ρ : CuspSub E a}, ρ.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR ρ, GlobalTheory.JSW.IsBCC F := by
    intro a ρ hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hρ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hπ φ hφ
  have hc' := hreg hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ hc.cont hc.bdd
  have hWc' := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ' hc'.cont hc'.bdd
  have hRI : ∀ {a : ℕ} (Φ : GA E a → ℂ), (∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
        ∀ u ∈ U, ∀ g, Φ (g * finGL E a u) = Φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w a, ∀ g, Φ (g * finGL E a (locGL E a w k)) = Φ g) →
      ∀ k : GL (Fin a) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v a) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit Φ (g * finGL E a k) = GlobalTheory.JSW.whit Φ g := by
    intro a Φ ⟨U, hUo, hUi⟩ hKi k hk1 hk2 g
    let stab : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, Φ (g * finGL E a k) = Φ g}
        mul_mem' := fun {a' c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
        one_mem' := fun g => by rw [map_one, mul_one]
        inv_mem' := fun {a'} ha g => by
          rw [← ha (g * finGL E a a'⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
    let V : Subgroup (GL (Fin a) (Af E)) := U ⊔ Subgroup.closure
      {k | ∃ w ∉ S, ∃ k' ∈ KGL w a, locGL E a w k' = k}
    have hVle : V ≤ stab := by
      refine sup_le (fun k hk => hUi k hk) (Subgroup.closure_le _ |>.2 ?_)
      rintro _ ⟨w, hw, k, hk, rfl⟩
      exact hKi w hw k hk
    have hVo : IsOpen (V : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (le_sup_left : U ≤ V) hUo
    have hVK : ∀ w ∉ S, ∀ k ∈ KGL w a, locGL E a w k ∈ V := fun w hw k hk =>
      (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
    obtain ⟨J, -, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hVo hVK
    have hkJ : k ∈ GlobalTheory.RSLocalPart.levelAt a S J := by
      refine ⟨hk1, fun v hv i j => ?_⟩
      have e1 := congrArg (fun M : GL (Fin a) (v.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hk2 v hv)
      have e2 : ((k.val - 1) i j) v = 0 := by
        have e1' : pLoc E v (k.val i j) = (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j := by simpa using e1
        change pLoc E v (k.val i j - (1 : Matrix (Fin a) (Fin a) (Af E)) i j) = 0
        rw [map_sub, e1', Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, map_zero]
      exact zero_le'
    have e : (fun z => Φ (z * finGL E a k)) = Φ := funext fun z => hVle (hJV hkJ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWK := hRI φ hU hK
  have hWK' := hRI φ' hU' hK'
  obtain ⟨h₀, hh₀, hκ₀, hW₀⟩ := h₀
  have hint : ∀ w ∉ S, ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) ∈ w.adicCompletionIntegers E := by
    intro w hw j
    have e1 := congrArg (fun M : GL (Fin (m + 1)) (w.adicCompletion E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) (hh₀ w hw)
    have e2 : pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
      simpa [GlobalTheory.ZEul.lastRow] using e1
    rw [e2, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨F, hFSB, hFc, hFr, hFpos, hFsc⟩ := GlobalTheory.FourierCell.exists_fourier_gauss_lattice E m S (GlobalTheory.ZEul.lastRow h₀) hint
  refine ⟨F, hFSB, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet, hDA, hDB⟩ := GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg E m r S φ φ' κ F hWc hWc' hW hW'
    hWK hWK' hmatch hκc hκ0 hκC ⟨h₀, hh₀, hκ₀, hW₀, hFpos⟩ hFc hFr μ 𝓕₀ h𝓕
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hdα hdβ

  have ev := GlobalTheory.CellEvalNM.uIntNM_cell_eval E m r S hψ ϖ hϖ α β φ φ' F hW hW' hWK hWK' (hshβ ϖ hϖ) (hshα ϖ hϖ)
    (fun a ha y hy => hFsc ϖ hϖ a ha y hy) x
  obtain ⟨hWbc, hFlc, hmeas, hinv, hbd⟩ := GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hW hW' hFc
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) := (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
    h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet

  have hlinD : ∀ (D : GA E (m + 1) → ℝ≥0∞) (c : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℝ≥0∞), Measurable D →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, D (u * g) = D g) →
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = c l * D g) →
      ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ ≠ ⊤ → (∑' l, c l) ≠ ⊤ → ∫⁻ g in 𝓕₀, D g ∂μ ≠ ⊤ := by
    intro D c hDm hDi hDc hD hc
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 D hDm hDi]
    have : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        c l * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ := by
      intro l
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← lintegral_const_mul'' _ hDm.aemeasurable]
      exact lintegral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => hDc g hg.2 l)
    simp_rw [this, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hc hD
  have hen : ∀ {a b : ℂ}, ‖a‖ = ‖b‖ → ‖a‖ₑ = ‖b‖ₑ := fun h => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]
  have hmD : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWbc.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have hmD' : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWc'.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have LA := hlinD _ _ (hmD _) (fun u hu g => by
      obtain ⟨h1, -, h3, h4, -⟩ := hinv u hu g
      rw [hen h1, h3, h4]) (fun g hg l => (ev g hg l).2.1) (hDA x)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + r + 1 + 1) S (by omega) (fun w i => (α w i : ℂ)) x hdα)
  have LB := hlinD _ _ (hmD' _) (fun u hu g => by
      obtain ⟨-, h2, h3, h4, -⟩ := hinv u hu g
      rw [hen h2, h3, h4]) (fun g hg l => (ev g hg l).2.2) (hDB π' hπ' hφ' hFSB x hx)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + 1) S le_rfl (fun w i => (β w i : ℂ)) x hdβ)
  refine ⟨LA, LB, ?_⟩

  have hDtr : ∀ (a b : ℂ) (s : ℝ) (g : GA E (m + 1)), (‖a‖ₑ ^ 2 * ‖b‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)).toReal =
      ‖a‖ ^ 2 * ‖b‖ * GlobalTheory.RSnm.detAbs g ^ s := by
    intro a b s g
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (GlobalTheory.RSnm.detAbs_pos g).le _)]
  have iA := integrable_toReal_of_lintegral_ne_top (hmD (x - ((r : ℝ) + 1))).aemeasurable LA
  have iB := integrable_toReal_of_lintegral_ne_top (hmD' x).aemeasurable LB
  have i12 : Integrable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((iA.add iB).div_const 2) (hmeas x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        simp only [Pi.add_apply, hDtr]
        exact hbd x g)
  have hl : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
      ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S,
        GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
      (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (β w i : ℂ)) x v) * I := by
    intro l
    rw [← integral_const_mul, ← hIC, ← integral_const_mul]
    refine integral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => ?_)
    dsimp only
    rw [(ev g hg.2 l).1, hfu g hg.2, hdet, mul_assoc]
  have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 _ (hmeas x) i12 (fun u hu g => (hinv u hu g).2.2.2.2 x)).2
  simp_rw [hl] at h
  rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  congr 1
  rw [← e.tsum_eq]
  exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
    (fun i => (β w i : ℂ)) x v) (fun i => rsTermNM_zero _ _ _ _) l).symm

end GlobalTheory.RSnmCells
