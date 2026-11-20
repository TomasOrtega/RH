import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HilbertLemmas

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section SplitHelpers

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

/- English proof (translation)
The claim follows from `(ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hph.neg)).measurable`.
-/
theorem splitT_meas_dens (ph : M → ℝ) (hph : Continuous ph) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) := (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hph.neg)).measurable

/- English proof (translation)
Unfold `wvol`. Use `withDensity_absolutelyContinuous' (splitT_meas_dens ph hph).aemeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[Real.exp_pos]`.
-/
theorem splitT_ac (ph : M → ℝ) (hph : Continuous ph) : vol n z ≪ wvol n z ph := by
  unfold wvol
  refine withDensity_absolutelyContinuous' (splitT_meas_dens ph hph).aemeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.exp_pos]

/- English proof (translation)
The claim follows from `(splitT_ac ph hph).ae_le h`.
-/
theorem splitT_ae {X : Type*} (ph : M → ℝ) (hph : Continuous ph) {F G : M → X}
    (h : F =ᵐ[wvol n z ph] G) : F =ᵐ[vol n z] G := (splitT_ac ph hph).ae_le h

/- English proof (translation)
Use `haveI := vol_isFiniteMeasureOnCompacts n z hz`. Unfold `wvol`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (Real.continuous_exp.comp hph.neg).continuousOn`. Establish `hC' : ∀ x ∈ K, Real.exp (-ph x) ≤ C` using `fun x hx => by`.

Establish `h1` using `hC x hx`. Rewrite `h1` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans h1`. Rewrite using `[withDensity_apply _ hK.isClosed.measurableSet]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem splitT_fin (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  unfold wvol
  refine ⟨fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (Real.continuous_exp.comp hph.neg).continuousOn
  have hC' : ∀ x ∈ K, Real.exp (-ph x) ≤ C := fun x hx => by
    have h1 := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z
      ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂vol n z :=
        setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal (hC' x hx)
    _ = ENNReal.ofReal C * vol n z K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/- English proof (translation)
Establish `hac : wvol n z ph ≪ vol n z` using `withDensity_absolutelyContinuous _ _`. Establish `hu' : AEStronglyMeasurable u (wvol n z ph)` using `hu.mono_ac hac`. Establish `he : ∀ x, (ENNReal.ofReal (Real.exp (-ph x))).toReal = Real.exp (-ph x)` using `fun x => ENNReal.toReal_ofReal (Real.exp_nonneg _)`. Establish `hm : AEStronglyMeasurable (fun x => ‖u x‖ ^ 2 * Real.exp (-ph x)) (vol n z)` using `(hu.norm.pow 2).mul (Real.continuous_exp.comp hph.neg).aestronglyMeasurable`. Establish `h0 : (0 : M → ℝ) ≤ᵐ[vol n z] fun x => ‖u x‖ ^ 2 * Real.exp (-ph x)` using `Filter.Eventually.of_forall fun x => by show (0 : ℝ) ≤ _`.

Check the signs of the components of the expression. Rewrite using `[memLp_two_iff_integrable_sq_norm hu']`. Unfold `wvol`. Rewrite using `[integrable_withDensity_iff (splitT_meas_dens ph hph) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]`. Simplify using `only [he]`.

Prove the components needed by the constructor for the conclusion. Introduce `hI`. Conclude with `(hasFiniteIntegral_iff_ofReal h0).1 hI.2`. Introduce `hI`. Conclude with `⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 hI⟩`.
-/
theorem splitT_memLp_iff {E : Type*} [NormedAddCommGroup E] (ph : M → ℝ) (hph : Continuous ph)
    (u : M → E) (hu : AEStronglyMeasurable u (vol n z)) :
    MemLp u 2 (wvol n z ph) ↔
      ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z < ⊤ := by
  have hac : wvol n z ph ≪ vol n z := withDensity_absolutelyContinuous _ _
  have hu' : AEStronglyMeasurable u (wvol n z ph) := hu.mono_ac hac
  have he : ∀ x, (ENNReal.ofReal (Real.exp (-ph x))).toReal = Real.exp (-ph x) :=
    fun x => ENNReal.toReal_ofReal (Real.exp_nonneg _)
  have hm : AEStronglyMeasurable (fun x => ‖u x‖ ^ 2 * Real.exp (-ph x)) (vol n z) :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp hph.neg).aestronglyMeasurable
  have h0 : (0 : M → ℝ) ≤ᵐ[vol n z] fun x => ‖u x‖ ^ 2 * Real.exp (-ph x) :=
    Filter.Eventually.of_forall fun x => by
      show (0 : ℝ) ≤ _
      positivity
  rw [memLp_two_iff_integrable_sq_norm hu']
  unfold wvol
  rw [integrable_withDensity_iff (splitT_meas_dens ph hph)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [he]
  constructor
  · intro hI
    exact (hasFiniteIntegral_iff_ofReal h0).1 hI.2
  · intro hI
    exact ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 hI⟩

/- English proof (translation)
Establish `hd : Measurable (fun x => (Real.exp (-ph x)).toNNReal)` using `(Real.continuous_exp.comp hph.neg).measurable.real_toNNReal`. Establish `hae : (fun a => ⟪(hF.toLp F) a, G a⟫_ℂ) =ᵐ[wvol n z ph] fun a => ⟪F a, G a⟫_ℂ` using `hF.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx]`. Rewrite using `[MeasureTheory.L2.inner_def, integral_congr_ae hae]`. Use `show ∫ a, ⟪F a, G a⟫_ℂ ∂((vol n z).withDensity fun x => ((Real.exp (-ph x)).toNNReal : ℝ≥0∞)) = _`. Rewrite using `[integral_withDensity_eq_integral_smul hd]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem splitT_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F : M → E) (hF : MemLp F 2 (wvol n z ph))
    (G : Lp E 2 (wvol n z ph)) :
    ⟪hF.toLp F, G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hd : Measurable (fun x => (Real.exp (-ph x)).toNNReal) :=
    (Real.continuous_exp.comp hph.neg).measurable.real_toNNReal
  have hae : (fun a => ⟪(hF.toLp F) a, G a⟫_ℂ) =ᵐ[wvol n z ph] fun a => ⟪F a, G a⟫_ℂ :=
    hF.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
  show ∫ a, ⟪F a, G a⟫_ℂ ∂((vol n z).withDensity fun x => ((Real.exp (-ph x)).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hd]
  congr 1
  funext x
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), Complex.real_smul]
  ring

/- English proof (translation)
Rewrite using `[splitT_inner ph hph F hF (hG.toLp G)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `h1` using `splitT_ae (n := n) (z := z) ph hph hG.coeFn_toLp`. Use `filter_upwards [h1] with x hx`. Rewrite using `[hx]`.
-/
theorem splitT_inner2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F G : M → E) (hF : MemLp F 2 (wvol n z ph))
    (hG : MemLp G 2 (wvol n z ph)) :
    ⟪hF.toLp F, hG.toLp G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  rw [splitT_inner ph hph F hF (hG.toLp G)]
  refine integral_congr_ae ?_
  have h1 := splitT_ae (n := n) (z := z) ph hph hG.coeFn_toLp
  filter_upwards [h1] with x hx
  rw [hx]

/- English proof (translation)
Use `HasCompactSupport.intro (K := ⋃ j, S j) (isCompact_iUnion hS) fun x hx => ?_` and prove the remaining obligations. Conclude with `h x fun j hj => hx (Set.mem_iUnion.2 ⟨j, hj⟩)`.
-/
theorem splitT_hcs {X : Type*} [Zero X] (u : M → X) (S : Fin n → Set M)
    (hS : ∀ j, IsCompact (S j)) (h : ∀ x, (∀ j, x ∉ S j) → u x = 0) : HasCompactSupport u := by
  refine HasCompactSupport.intro (K := ⋃ j, S j) (isCompact_iUnion hS) fun x hx => ?_
  exact h x fun j hj => hx (Set.mem_iUnion.2 ⟨j, hj⟩)

/- English proof (translation)
Use `first`. Consider the case `exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)`. Consider the case `exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp (continuous_pi h)`. Consider the case `exact continuous_induced_rng.2 (continuous_pi h)`.
-/
theorem splitT_cont (f : M → V n) (h : ∀ j, Continuous fun x => f x j) : Continuous f := by
  first
  | exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)
  | exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp (continuous_pi h)
  | exact continuous_induced_rng.2 (continuous_pi h)

/- English proof (translation)
Unfold `IsWeakS at h ⊢`. Introduce `φ hφ j k`. Rewrite using `[← h φ hφ j k]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hFG] with x hx`.

Rewrite using `[hx]`.
-/
theorem splitT_weakS (F G : M → V n) (hFG : F =ᵐ[vol n z] G) (σ : M → Fin n → Fin n → ℂ)
    (h : IsWeakS n z F σ) : IsWeakS n z G σ := by
  unfold IsWeakS at h ⊢
  intro φ hφ j k
  rw [← h φ hφ j k]
  refine integral_congr_ae ?_
  filter_upwards [hFG] with x hx
  rw [hx]

end SplitHelpers

def splitTestSub {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) :
    Submodule ℂ (M → ℂ) where
  carrier := {g | IsTest n z g}
  add_mem' := fun {a b} ha hb => ⟨Smooth.add n z a b ha.1 hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨Smooth.const n z 0, HasCompactSupport.zero⟩
  smul_mem' := fun c g hg => ⟨Smooth.mul n z (fun _ => c) g (Smooth.const n z c) hg.1,
    hg.2.mul_left (f := fun _ => c)⟩

/- English proof (translation)
Establish `key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source, fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0`. Introduce `h`. Take `⟨he, hx'⟩` from `Classical.choose_spec h`. Use `set e := Classical.choose h`. Establish `hzx : z x = e x` using `he hx'`.

Establish `hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ)`. Rewrite using `[hzx]`. Establish `hopen : IsOpen K0ᶜ` using `hK0.isClosed.isOpen_compl`. Establish `hc : ContinuousAt e.symm (e x)` using `e.continuousAt_symm (e.map_source hx')`. Establish `hmem : K0ᶜ ∈ 𝓝 (e.symm (e x))`.

Rewrite using `[e.left_inv hx']`. Conclude with `hopen.mem_nhds hx`. Use `filter_upwards [hc.preimage_mem_nhds hmem] with y hy`. Conclude with `hu _ hy`. Rewrite using `[hev.fderiv_eq]`.

Conclude with `fderiv_const_apply _`. Unfold `d db wd wdb`. Prove the components needed by the constructor for the conclusion. Use `split_ifs with h`. Rewrite using `[key h]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `split_ifs with h`. Rewrite using `[key h]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
private theorem d_db_eq_zero_of_not_mem_compact_support {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by
  have key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source,
      fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0 := by
    intro h
    obtain ⟨he, hx'⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx'
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
      rw [hzx]
      have hopen : IsOpen K0ᶜ := hK0.isClosed.isOpen_compl
      have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx')
      have hmem : K0ᶜ ∈ 𝓝 (e.symm (e x)) := by
        rw [e.left_inv hx']
        exact hopen.mem_nhds hx
      filter_upwards [hc.preimage_mem_nhds hmem] with y hy
      exact hu _ hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold d db wd wdb
  constructor
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
  · split_ifs with h
    · rw [key h]
      simp
    · rfl

/- English proof (translation)
Unfold `Smooth at hu ⊢`. Introduce `e he`. Establish `hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ))` using `by first`. Consider the case `fun_prop`. Consider the case `exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)`.

Use `(hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_` and prove the remaining obligations. Simplify using `[Function.comp]`.
-/
private theorem smooth_exp_ofReal_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℝ)
    (hu : Smooth n z (fun y => (u y : ℂ))) : Smooth n z (fun y => (Real.exp (u y) : ℂ)) := by
  unfold Smooth at hu ⊢
  intro e he
  have hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ)) := by
    first
    | fun_prop
    | exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)
  refine (hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_
  simp [Function.comp]

/- English proof (translation)
Unfold `SplitTestStatement`. Unfold `KSubStatement at hK`. Unfold `WeakSSmoothStatement at hWS`. Unfold `SbarDbarStatement at hSD`. Unfold `TStarIbpStatement at hTI`.

Introduce `z hz ph₁ ph₂ v f hph₁ hph₂ hv hvS hf`. Establish `hc1 : Continuous ph₁` using `Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₁ x : ℂ)) hph₁)`. Establish `hc2 : Continuous ph₂` using `Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₂ x : ℂ)) hph₂)`. Use `haveI hfin2 : IsFiniteMeasureOnCompacts (wvol n z ph₂) := splitT_fin hz ph₂ hc2`. Use `haveI hfin1 : IsFiniteMeasureOnCompacts (wvol n z ph₁) := splitT_fin hz ph₁ hc1`.

Take `⟨K, hKc, hKiff⟩` from `hK z hz ph₂ hc2`. Use `haveI : CompleteSpace K := hKc.completeSpace_coe`. Unfold `IsTestForm at hf`. Establish `hfcont : Continuous f` using `splitT_cont f fun j => Ck.continuous n z hz 2 _ (hf j).1`. Establish `hfsupp : HasCompactSupport f`.

Use `splitT_hcs f (fun j => tsupport fun x => f x j) (fun j => (hf j).2) fun x hx => ?_` and prove the remaining obligations. Use extensionality with `j`. Establish `h0` using `image_eq_zero_of_notMem_tsupport (hx j)`. Simplify using `using h0`. Establish `hfL : MemLp f 2 (wvol n z ph₂)` using `hfcont.memLp_of_hasCompactSupport hfsupp`.

Establish `hE1 : Smooth n z (fun y => (Real.exp (ph₁ y) : ℂ))` using `smooth_exp_ofReal_of_smooth n z ph₁ hph₁`. Establish `hE2 : Smooth n z (fun y => (Real.exp (-ph₂ y) : ℂ))`. Apply `smooth_exp_ofReal_of_smooth n z (fun y => -ph₂ y)` to reduce the goal to its premises. Use `show Smooth n z (fun y => ((-ph₂ y : ℝ) : ℂ))`. Establish `h` using `Smooth.mul n z (fun _ => (-1 : ℂ)) (fun y => (ph₂ y : ℂ)) (Smooth.const n z (-1)) hph₂`.

Establish `he : (fun y => ((-ph₂ y : ℝ) : ℂ)) = fun y => (-1 : ℂ) * (ph₂ y : ℂ)`. Use function extensionality and compare the values at `y`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`.

Conclude with `h`. Establish `hprod : ∀ j, Ck n z 2 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)` using `fun j => Ck.mul n z 2 _ _ (Smooth.ck n z 2 _ hE2) (hf j).1`. Establish `hdj : ∀ j, Continuous (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j))` using `fun j => Ck.continuous n z hz 1 _ (Ck.d n z 1 j _ (hprod j))`. Establish `htc : Continuous (tstar n z ph₁ ph₂ f)`. Unfold `tstar`.

Conclude with `((Smooth.continuous n z hz _ hE1).mul (continuous_finset_sum _ fun j _ => hdj j)).neg`. Establish `hoff : ∀ j x, x ∉ tsupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) → d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0` using `fun j x hx => (d_db_eq_zero_of_not_mem_compact_support n z (tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) ((hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) _ (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).1`. Establish `htsupp : HasCompactSupport (tstar n z ph₁ ph₂ f)`. Use `splitT_hcs _ (fun j => tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) (fun j => (hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) fun x hx => ?_` and prove the remaining obligations. Establish `h0 : ∀ j, d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0` using `fun j => hoff j x (hx j)`.

Unfold `tstar`. Simplify using `only [h0, Finset.sum_const_zero, mul_zero, neg_zero]`. Establish `hMF : MemWeightedL2 n z (tstar n z ph₁ ph₂ f) ph₁`. Establish `hm : MemLp (tstar n z ph₁ ph₂ f) 2 (wvol n z ph₁)` using `htc.memLp_of_hasCompactSupport htsupp`. Unfold `MemWeightedL2 wint`.

Conclude with `⟨htc.aestronglyMeasurable, (splitT_memLp_iff ph₁ hc1 _ htc.aestronglyMeasurable).1 hm⟩`. Unfold `MemWeightedL2OneForm nV at hv`. Establish `hv' : MemLp v 2 (wvol n z ph₂)` using `(splitT_memLp_iff ph₂ hc2 v hv.1).2 hv.2`. Establish `hVK : hv'.toLp v ∈ K` using `(hKiff _).2 (splitT_weakS v _ (splitT_ae ph₂ hc2 hv'.coeFn_toLp).symm 0 hvS)`. Take `⟨F₁, hF₁K, G, hGperp, hdec⟩` from `K.exists_add_mem_mem_orthogonal (hfL.toLp f)`.

Establish `hoffg : ∀ g : M → ℂ, HasCompactSupport g → ∀ j x, x ∉ tsupport g → db n z j g x = 0` using `fun g hg j x hx => (d_db_eq_zero_of_not_mem_compact_support n z (tsupport g) hg g (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).2`. Use `⟨hMF, fun x => F₁ x, ?_, (hKiff F₁).1 hF₁K, ?_, ?_⟩` and prove the remaining obligations. Unfold `MemWeightedL2OneForm nV`. Establish `ha : AEStronglyMeasurable (fun x => F₁ x) (vol n z)` using `(Lp.aestronglyMeasurable F₁).mono_ac (splitT_ac ph₂ hc2)`. Conclude with `⟨ha, (splitT_memLp_iff ph₂ hc2 _ ha).1 (Lp.memLp F₁)⟩`.

Unfold `IsWeakAdj`. Introduce `g hg`. Unfold `IsTest at hg`. Establish `hDc : Continuous (dbarF n z g)` using `splitT_cont _ fun j => Smooth.continuous n z hz _ (Smooth.db n z j g hg.1)`. Establish `hDs : HasCompactSupport (dbarF n z g)`.

Use `splitT_hcs _ (fun _ : Fin n => tsupport g) (fun _ => hg.2) fun x hx => ?_` and prove the remaining obligations. Use `first`. Consider the case `exact PiLp.ext fun j => hoffg g hg.2 j x (hx j)`. Consider the case `(ext j; exact hoffg g hg.2 j x (hx j))`. Establish `hDg : MemLp (dbarF n z g) 2 (wvol n z ph₂)` using `hDc.memLp_of_hasCompactSupport hDs`.

Establish `hW` using `hWS z hz (dbarF n z g) fun j => Smooth.ck n z 1 _ (Smooth.db n z j g hg.1)`. Establish `hsbar : sbar n z (dbarF n z g) = 0` using `funext fun x => hSD z hz g (Smooth.ck n z 2 g hg.1) x`. Rewrite `hW` using `[hsbar]`. Establish `hDK : hDg.toLp (dbarF n z g) ∈ K` using `(hKiff _).2 (splitT_weakS _ _ (splitT_ae ph₂ hc2 hDg.coeFn_toLp).symm 0 hW)`. Establish `hck1 : CkR n z 1 ph₁` using `Smooth.ck n z 1 _ hph₁`.

Establish `hck2 : CkR n z 1 ph₂` using `Smooth.ck n z 1 _ hph₂`. Establish `hfc : ∀ j, Ck n z 1 (fun x => f x j) ∧ HasCompactSupport (fun x => f x j)` using `fun j => ⟨Ck.mono n z 1 2 (by norm_num) _ (hf j).1, (hf j).2⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hDK hGperp, add_zero]`. Use `_ = ∫ x, ⟪dbarF n z g x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z := splitT_inner2 ph₂ hc2 _ _ hDg hfL`.

Use `_ = ∫ x, conj ((∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ)) ∂vol n z := by`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[map_mul, Complex.conj_ofReal, map_sum, PiLp.inner_apply]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj]`. Use `show ⟪db n z j g x, f x j⟫_ℂ = _`. Use `first`. Consider the case `rfl`.

Consider the case `(simp only [RCLike.inner_apply]; ring)`. Consider the case `(simp only [RCLike.inner_apply])`. Consider the case `(simp [mul_comm])`. Use `_ = conj (∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z) := integral_conj`. Use `_ = conj (∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z) := by`.

Rewrite using `[hTI z hz ph₁ ph₂ g f hck1 hck2 (Smooth.ck n z 1 g hg.1) hfc]`. Use `_ = ∫ x, conj (g x) * tstar n z ph₁ ph₂ f x * (Real.exp (-ph₁ x) : ℂ) ∂vol n z := by`. Rewrite using `[← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Establish `e1 : ipV n z v f ph₂ = ⟪hv'.toLp v, hfL.toLp f⟫_ℂ`. Unfold `ipV`. Conclude with `(splitT_inner2 ph₂ hc2 v f hv' hfL).symm`. Establish `e2 : ipV n z v (fun x => F₁ x) ph₂ = ⟪hv'.toLp v, F₁⟫_ℂ`.

Unfold `ipV`. Conclude with `(splitT_inner ph₂ hc2 v hv' F₁).symm`. Rewrite using `[e1, e2, hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hVK hGperp, add_zero]`.
-/
theorem splitTest (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hK : KSubStatement n M) (hWS : WeakSSmoothStatement n M)
    (hSD : SbarDbarStatement n M) (hTI : TStarIbpStatement n M) : SplitTestStatement n M := by
  unfold SplitTestStatement
  unfold KSubStatement at hK
  unfold WeakSSmoothStatement at hWS
  unfold SbarDbarStatement at hSD
  unfold TStarIbpStatement at hTI
  intro z hz ph₁ ph₂ v f hph₁ hph₂ hv hvS hf
  have hc1 : Continuous ph₁ :=
    Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₁ x : ℂ)) hph₁)
  have hc2 : Continuous ph₂ :=
    Complex.continuous_re.comp (Smooth.continuous n z hz (fun x => (ph₂ x : ℂ)) hph₂)
  haveI hfin2 : IsFiniteMeasureOnCompacts (wvol n z ph₂) := splitT_fin hz ph₂ hc2
  haveI hfin1 : IsFiniteMeasureOnCompacts (wvol n z ph₁) := splitT_fin hz ph₁ hc1
  obtain ⟨K, hKc, hKiff⟩ := hK z hz ph₂ hc2
  haveI : CompleteSpace K := hKc.completeSpace_coe
  unfold IsTestForm at hf
  have hfcont : Continuous f := splitT_cont f fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hfsupp : HasCompactSupport f := by
    refine splitT_hcs f (fun j => tsupport fun x => f x j) (fun j => (hf j).2) fun x hx => ?_
    ext j
    have h0 := image_eq_zero_of_notMem_tsupport (hx j)
    simpa using h0
  have hfL : MemLp f 2 (wvol n z ph₂) := hfcont.memLp_of_hasCompactSupport hfsupp

  have hE1 : Smooth n z (fun y => (Real.exp (ph₁ y) : ℂ)) := smooth_exp_ofReal_of_smooth n z ph₁ hph₁
  have hE2 : Smooth n z (fun y => (Real.exp (-ph₂ y) : ℂ)) := by
    apply smooth_exp_ofReal_of_smooth n z (fun y => -ph₂ y)
    show Smooth n z (fun y => ((-ph₂ y : ℝ) : ℂ))
    have h := Smooth.mul n z (fun _ => (-1 : ℂ)) (fun y => (ph₂ y : ℂ)) (Smooth.const n z (-1)) hph₂
    have he : (fun y => ((-ph₂ y : ℝ) : ℂ)) = fun y => (-1 : ℂ) * (ph₂ y : ℂ) := by
      funext y
      push_cast
      ring
    rw [he]
    exact h
  have hprod : ∀ j, Ck n z 2 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) := fun j =>
    Ck.mul n z 2 _ _ (Smooth.ck n z 2 _ hE2) (hf j).1
  have hdj : ∀ j, Continuous (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)) := fun j =>
    Ck.continuous n z hz 1 _ (Ck.d n z 1 j _ (hprod j))
  have htc : Continuous (tstar n z ph₁ ph₂ f) := by
    unfold tstar
    exact ((Smooth.continuous n z hz _ hE1).mul (continuous_finset_sum _ fun j _ => hdj j)).neg
  have hoff : ∀ j x, x ∉ tsupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) →
      d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0 := fun j x hx =>
    (d_db_eq_zero_of_not_mem_compact_support n z (tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)
      ((hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) _
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).1
  have htsupp : HasCompactSupport (tstar n z ph₁ ph₂ f) := by
    refine splitT_hcs _ (fun j => tsupport fun y => (Real.exp (-ph₂ y) : ℂ) * f y j)
      (fun j => (hf j).2.mul_left (f := fun y => (Real.exp (-ph₂ y) : ℂ))) fun x hx => ?_
    have h0 : ∀ j, d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x = 0 := fun j =>
      hoff j x (hx j)
    unfold tstar
    simp only [h0, Finset.sum_const_zero, mul_zero, neg_zero]
  have hMF : MemWeightedL2 n z (tstar n z ph₁ ph₂ f) ph₁ := by
    have hm : MemLp (tstar n z ph₁ ph₂ f) 2 (wvol n z ph₁) := htc.memLp_of_hasCompactSupport htsupp
    unfold MemWeightedL2 wint
    exact ⟨htc.aestronglyMeasurable,
      (splitT_memLp_iff ph₁ hc1 _ htc.aestronglyMeasurable).1 hm⟩

  unfold MemWeightedL2OneForm nV at hv
  have hv' : MemLp v 2 (wvol n z ph₂) := (splitT_memLp_iff ph₂ hc2 v hv.1).2 hv.2
  have hVK : hv'.toLp v ∈ K :=
    (hKiff _).2 (splitT_weakS v _ (splitT_ae ph₂ hc2 hv'.coeFn_toLp).symm 0 hvS)

  obtain ⟨F₁, hF₁K, G, hGperp, hdec⟩ := K.exists_add_mem_mem_orthogonal (hfL.toLp f)
  have hoffg : ∀ g : M → ℂ, HasCompactSupport g → ∀ j x, x ∉ tsupport g → db n z j g x = 0 :=
    fun g hg j x hx =>
      (d_db_eq_zero_of_not_mem_compact_support n z (tsupport g) hg g (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx j).2
  refine ⟨hMF, fun x => F₁ x, ?_, (hKiff F₁).1 hF₁K, ?_, ?_⟩
  · unfold MemWeightedL2OneForm nV
    have ha : AEStronglyMeasurable (fun x => F₁ x) (vol n z) :=
      (Lp.aestronglyMeasurable F₁).mono_ac (splitT_ac ph₂ hc2)
    exact ⟨ha, (splitT_memLp_iff ph₂ hc2 _ ha).1 (Lp.memLp F₁)⟩
  · unfold IsWeakAdj
    intro g hg
    unfold IsTest at hg
    have hDc : Continuous (dbarF n z g) :=
      splitT_cont _ fun j => Smooth.continuous n z hz _ (Smooth.db n z j g hg.1)
    have hDs : HasCompactSupport (dbarF n z g) := by
      refine splitT_hcs _ (fun _ : Fin n => tsupport g) (fun _ => hg.2) fun x hx => ?_
      first
      | exact PiLp.ext fun j => hoffg g hg.2 j x (hx j)
      | (ext j; exact hoffg g hg.2 j x (hx j))
    have hDg : MemLp (dbarF n z g) 2 (wvol n z ph₂) := hDc.memLp_of_hasCompactSupport hDs
    have hW := hWS z hz (dbarF n z g) fun j => Smooth.ck n z 1 _ (Smooth.db n z j g hg.1)
    have hsbar : sbar n z (dbarF n z g) = 0 := funext fun x => hSD z hz g (Smooth.ck n z 2 g hg.1) x
    rw [hsbar] at hW
    have hDK : hDg.toLp (dbarF n z g) ∈ K :=
      (hKiff _).2 (splitT_weakS _ _ (splitT_ae ph₂ hc2 hDg.coeFn_toLp).symm 0 hW)
    have hck1 : CkR n z 1 ph₁ := Smooth.ck n z 1 _ hph₁
    have hck2 : CkR n z 1 ph₂ := Smooth.ck n z 1 _ hph₂
    have hfc : ∀ j, Ck n z 1 (fun x => f x j) ∧ HasCompactSupport (fun x => f x j) := fun j =>
      ⟨Ck.mono n z 1 2 (by norm_num) _ (hf j).1, (hf j).2⟩
    calc ∫ x, ⟪dbarF n z g x, F₁ x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z
        = ⟪hDg.toLp (dbarF n z g), F₁⟫_ℂ := (splitT_inner ph₂ hc2 _ hDg F₁).symm
      _ = ⟪hDg.toLp (dbarF n z g), hfL.toLp f⟫_ℂ := by
          rw [hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hDK hGperp, add_zero]
      _ = ∫ x, ⟪dbarF n z g x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z :=
          splitT_inner2 ph₂ hc2 _ _ hDg hfL
      _ = ∫ x, conj ((∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ)) ∂vol n z := by
          congr 1
          funext x
          rw [map_mul, Complex.conj_ofReal, map_sum, PiLp.inner_apply]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, Complex.conj_conj]
          show ⟪db n z j g x, f x j⟫_ℂ = _
          first
          | rfl
          | (simp only [RCLike.inner_apply]; ring)
          | (simp only [RCLike.inner_apply])
          | (simp [mul_comm])
      _ = conj (∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z) :=
          integral_conj
      _ = conj (∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z) := by
          rw [hTI z hz ph₁ ph₂ g f hck1 hck2 (Smooth.ck n z 1 g hg.1) hfc]
      _ = ∫ x, conj (g x) * tstar n z ph₁ ph₂ f x * (Real.exp (-ph₁ x) : ℂ) ∂vol n z := by
          rw [← integral_conj]
          congr 1
          funext x
          rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  · have e1 : ipV n z v f ph₂ = ⟪hv'.toLp v, hfL.toLp f⟫_ℂ := by
      unfold ipV
      exact (splitT_inner2 ph₂ hc2 v f hv' hfL).symm
    have e2 : ipV n z v (fun x => F₁ x) ph₂ = ⟪hv'.toLp v, F₁⟫_ℂ := by
      unfold ipV
      exact (splitT_inner ph₂ hc2 v hv' F₁).symm
    rw [e1, e2, hdec, inner_add_right, Submodule.inner_right_of_mem_orthogonal hVK hGperp, add_zero]

end

end ReciprocityTheory.L2DbarEstimates.F
