import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowLine
import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThKF0.Split

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `: BorelSpace (mixedEmbedding.mixedSpace F)` using `inferInstance`. Conclude with `Pi.borelSpace`.
-/
theorem borelV : BorelSpace (V F κ) := by
  have : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  exact Pi.borelSpace

/- English proof (translation)
Use `(continuous_comp_splitE F κ Φ hΦ).comp (continuous_splitE_symm F κ)` as an intermediate fact. Simplify `this` using `only [Function.comp_def, AddEquiv.apply_symm_apply]`.
-/
theorem continuous_of_mem {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have := (continuous_comp_splitE F κ Φ hΦ).comp (continuous_splitE_symm F κ)
  simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using this

/- English proof (translation)
Use `haveI := volume_isAddHaar F κ`. Use `haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`.

Use `letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable`.

Use `set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν`. Use `haveI : SFinite ν := inferInstance`. Use `haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Use `haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd`. Use `haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance`.

Use `haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν`. Use `haveI hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) := (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)`. Set `eh` to `Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)`. Use `haveI : SecondCountableTopology (κ → AdeleRing (𝓞 F) F) := eh.symm.secondCountableTopology`. Establish `hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞, ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν)` using `fun h => lintegral_map_equiv h eh.toMeasurableEquiv`.

Establish `hgc : Continuous g` using `hg.1.continuous`. Establish `hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν < ⊤`. Establish `h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤` using `((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2`. Use `(lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)` and prove the remaining obligations. Rewrite using `[enorm_mul, sq]`.

Use `haveI : μ.IsAddHaarMeasure := hμ`. Rewrite using `[nsq, Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (splitE F κ)), lintegral_smul_measure, hint]`. Establish `e1 : ∀ p, ‖pureA F u g (splitE F κ p)‖ₑ ^ 2 = ‖u p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2`. Introduce `p`. Rewrite using `[pureA_splitE, enorm_mul, mul_pow]`.

Repeatedly rewrite using `[e1]`. Rewrite using `[lintegral_prod_mul (hu.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable]`. Conclude with `ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hu2 hC)`.
-/
theorem nsq_pure_lt_top {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {u : V F κ → ℂ} (hu : Continuous u)
    (hu2 : ∫⁻ z, ‖u z‖ₑ ^ 2 < ⊤) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : nsq μ (pureA F u g) < ⊤ := by
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  haveI hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let eh := Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)
  haveI : SecondCountableTopology (κ → AdeleRing (𝓞 F) F) := eh.symm.secondCountableTopology
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h eh.toMeasurableEquiv
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν < ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  haveI : μ.IsAddHaarMeasure := hμ
  rw [nsq, Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (splitE F κ)), lintegral_smul_measure, hint]
  have e1 : ∀ p, ‖pureA F u g (splitE F κ p)‖ₑ ^ 2 = ‖u p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
    intro p
    rw [pureA_splitE, enorm_mul, mul_pow]
  simp_rw [e1]
  rw [lintegral_prod_mul (hu.measurable.enorm.pow_const 2).aemeasurable
    (hgc.measurable.enorm.pow_const 2).aemeasurable]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hu2 hC)

/- English proof (translation)
Simplify using `only [enorm_eq_nnnorm]`. Establish `: ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2`. Rewrite using `[← NNReal.coe_le_coe]`. Use `push_cast`. Establish `h` using `norm_add_le a b`.

Establish `h0` using `norm_nonneg (a + b)`. Use polynomial arithmetic with `[sq_nonneg (‖a‖ - ‖b‖)]`. Conclude with `this` after adjusting the coercions.
-/
theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [enorm_eq_nnnorm]
  have : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have h := norm_add_le a b
    have h0 := norm_nonneg (a + b)
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact_mod_cast this

omit [Fintype κ] in
/- English proof (translation)
Use `letI mA : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Unfold `nsq`. Rewrite using `[← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ (by simp), ← lintegral_add_left ((hΦ.measurable.enorm.pow_const 2).const_mul 2)]`. Conclude with `lintegral_mono fun x => enorm_add_sq_le _ _`.
-/
theorem nsq_add_le (μ : @Measure (κ → AF F) (borel _)) {Φ : (κ → AF F) → ℂ} (hΦ : Continuous Φ) (Ψ : (κ → AF F) → ℂ) :
    nsq μ (Φ + Ψ) ≤ 2 * nsq μ Φ + 2 * nsq μ Ψ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  unfold nsq
  rw [← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ (by simp),
    ← lintegral_add_left ((hΦ.measurable.enorm.pow_const 2).const_mul 2)]
  exact lintegral_mono fun x => enorm_add_sq_le _ _

omit [Fintype κ] in
/- English proof (translation)
Unfold `nsq`. Rewrite using `[← lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]`.
-/
theorem nsq_smul (μ : @Measure (κ → AF F) (borel _)) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    nsq μ (c • Φ) = ‖c‖ₑ ^ 2 * nsq μ Φ := by
  unfold nsq
  rw [← lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Use `haveI := volume_isAddHaar F κ`. Use `haveI := borelV (F := F) (κ := κ)`.

Use `nsq_pure_lt_top hμ f.continuous ?_ hg` and prove the remaining obligations. Use `(f.memLp 2 (volume : Measure (V F κ))).2` as an intermediate fact. Establish `h2` using `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) this`. Simplify using `using h2`. Consider the case `zero => simp [nsq]`.

Consider the case `add x x' hx _ h h'`. Conclude with `(nsq_add_le μ (continuous_of_mem hx) x').trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h, ENNReal.mul_lt_top (by simp) h'⟩)`. Consider the case `smul a x _ h => rw [nsq_smul]; exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) h`.
-/
theorem nsq_lt_top {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    nsq μ Φ < ⊤ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    haveI := volume_isAddHaar F κ
    haveI := borelV (F := F) (κ := κ)
    refine nsq_pure_lt_top hμ f.continuous ?_ hg
    have := (f.memLp 2 (volume : Measure (V F κ))).2
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) this
    simpa using h2
  | zero => simp [nsq]
  | add x x' hx _ h h' =>
    exact (nsq_add_le μ (continuous_of_mem hx) x').trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h, ENNReal.mul_lt_top (by simp) h'⟩)
  | smul a x _ h => rw [nsq_smul]; exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) h

/- English proof (translation)
Use `haveI := volume_isAddHaar F κ`. Use `haveI := borelV (F := F) (κ := κ)`. Use `⟨Module.finrank ℝ (V F κ) + 1, fun K => ?_⟩` and prove the remaining obligations. Establish `h` using `(integrable_one_add_norm (E := V F κ) (μ := volume) (r := ((2 * (Module.finrank ℝ (V F κ) + 1) : ℕ) : ℝ)) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (V F κ))])).const_mul (K ^ 2)`. Use `lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_)) h.2` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, ← enorm_pow, ← Complex.ofReal_pow, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real, mul_pow, inv_pow, ← pow_mul, mul_comm _ 2]`.
-/
theorem weight_lt_top : ∃ k : ℕ, ∀ K : ℝ, ∫⁻ z : V F κ, ‖((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 < ⊤ := by
  haveI := volume_isAddHaar F κ
  haveI := borelV (F := F) (κ := κ)
  refine ⟨Module.finrank ℝ (V F κ) + 1, fun K => ?_⟩
  have h := (integrable_one_add_norm (E := V F κ) (μ := volume) (r := ((2 * (Module.finrank ℝ (V F κ) + 1) : ℕ) : ℝ))
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (V F κ))])).const_mul (K ^ 2)
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_)) h.2
  beta_reduce
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← enorm_pow, ← Complex.ofReal_pow, ← ofReal_norm_eq_enorm,
    ← ofReal_norm_eq_enorm, Complex.norm_real, mul_pow, inv_pow, ← pow_mul, mul_comm _ 2]

omit [Fintype κ] in
/- English proof (translation)
The claim follows from `RingEquiv.apply_symm_apply _ _`.
-/
theorem evI_inf (a : mixedEmbedding.mixedSpace F) : evI F (inf a) = a := RingEquiv.apply_symm_apply _ _

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a`. Rewrite using `[← map_mul, ← Algebra.smul_def]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(0 : Af F) = 0 * 0`.

Rewrite using `[mul_zero]`.
-/
theorem inf_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : inf (t • a) = realAd F t * inf a := by
  refine Prod.ext ?_ ?_
  · change _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, ← Algebra.smul_def]; rfl
  · change (0 : Af F) = 0 * 0
    rw [mul_zero]

omit [Fintype κ] in
/- English proof (translation)
The claim follows from `Prod.ext (funext fun i => inf_smul t (w.1 i)) (funext fun i => inf_smul t (w.2 i))`.
-/
theorem emb_smul (t : ℝ) (w : V F κ × V F κ) : emb (t • w) = realAd F t • emb w :=
  Prod.ext (funext fun i => inf_smul t (w.1 i)) (funext fun i => inf_smul t (w.2 i))

omit [Fintype κ] in
/- English proof (translation)
Introduce `u hu` and use `funext fun i => by have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm) refine Prod.ext ?_ ?_ · change u.1 * _ = 0 rw [h, zero_mul] · change u.2 * 0 = 0 rw [mul_zero]`.
-/
theorem at_inf (a : V F κ) : At (evI F) (fun i => inf (a i)) := fun u hu => funext fun i => by
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

def qc (w : V F κ × V F κ) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, w.1 i * w.2 i)

/- English proof (translation)
Use `schr_line ψ hψ _ _ (at_inf w.1) (at_inf w.2) f g x t` as an intermediate fact. Simplify using `only [evI_inf] at this`. Rewrite using `[emb_smul]`. Conclude with `this`.
-/
theorem schr_emb {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ)
    (x : κ → AF F) (t : ℝ) : schr ψ (emb (t • w)) (pureA F f g) x =
      lineFn f w.1 (linForm w.2) (qc w) (fun i => evI F (x i)) t * g (fun i => (x i).2) := by
  have := schr_line ψ hψ _ _ (at_inf w.1) (at_inf w.2) f g x t
  simp only [evI_inf] at this
  rw [emb_smul]
  exact this

def dS (w : V F κ × V F κ) (f : SInf F κ) : SInf F κ :=
  ∂_{w.1} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (linForm w.2) f

/- English proof (translation)
Simplify using `[dS, SchwartzMap.smulLeftCLM_apply_apply (linForm w.2).hasTemperateGrowth, SchwartzMap.lineDerivOp_apply_eq_fderiv]`.
-/
theorem dS_apply (w : V F κ × V F κ) (f : SInf F κ) (p : V F κ) :
    dS w f p = fderiv ℝ f p w.1 + -(2 * Real.pi * Complex.I) * ((linForm w.2 p : ℝ) * f p) := by
  simp [dS, SchwartzMap.smulLeftCLM_apply_apply (linForm w.2).hasTemperateGrowth, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/- English proof (translation)
Simplify using `only [schr_emb hψ]`. Use `((hasDerivAt_lineFn f w.1 (linForm w.2) (qc w) (fun i => evI F (x i)) 0).mul_const _).congr_deriv ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = dS w f (fun i => evI F (x i)) * _`. Rewrite using `[dS_apply, lineD]`. Simplify using the standard rewrite rules.

Use `left`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ)
    (x : κ → AF F) : HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) (pureA F f g) x) (pureA F (dS w f) g x) 0 := by
  simp only [schr_emb hψ]
  refine ((hasDerivAt_lineFn f w.1 (linForm w.2) (qc w) (fun i => evI F (x i)) 0).mul_const _).congr_deriv ?_
  change _ = dS w f (fun i => evI F (x i)) * _
  rw [dS_apply, lineD]
  simp
  left; ring

/- English proof (translation)
The claim follows from `funext fun x => (hasDerivAt_pure hψ w f g x).deriv`.
-/
theorem dR_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    dR ψ w (pureA F f g) = pureA F (dS w f) g := funext fun x => (hasDerivAt_pure hψ w f g x).deriv

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[schr, mul_add]`.
-/
theorem schr_add (ψ : AddChar (AF F) ℂ) (w : Pt F κ) (Φ Ψ : (κ → AF F) → ℂ) :
    schr ψ w (Φ + Ψ) = schr ψ w Φ + schr ψ w Ψ := by funext x; simp [schr, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[schr, mul_left_comm]`.
-/
theorem schr_smul (ψ : AddChar (AF F) ℂ) (w : Pt F κ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    schr ψ w (c • Φ) = c • schr ψ w Φ := by funext x; simp [schr, mul_left_comm]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Conclude with `⟨_, Submodule.subset_span ⟨dS w f, g, hg, rfl⟩, hasDerivAt_pure hψ w f g⟩`. Consider the case `zero => exact ⟨0, zero_mem _, fun x => by simpa [schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩`.

Consider the case `add a b _ _ h h'`. Take `⟨a', ha, h⟩` from `h`. Take `⟨b', hb, h'⟩` from `h'`. Conclude with `⟨a' + b', add_mem ha hb, fun x => by simp only [schr_add]; exact (h x).fun_add (h' x)⟩`. Consider the case `smul c a _ h`.

Take `⟨a', ha, h⟩` from `h`. Conclude with `⟨c • a', Submodule.smul_mem _ c ha, fun x => by simp only [schr_smul]; exact (h x).const_mul c⟩`.
-/
theorem exists_deriv {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ Φ' ∈ schA F κ, ∀ x, HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (Φ' x) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨dS w f, g, hg, rfl⟩, hasDerivAt_pure hψ w f g⟩
  | zero => exact ⟨0, zero_mem _, fun x => by simpa [schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add a b _ _ h h' =>
    obtain ⟨a', ha, h⟩ := h
    obtain ⟨b', hb, h'⟩ := h'
    exact ⟨a' + b', add_mem ha hb, fun x => by simp only [schr_add]; exact (h x).fun_add (h' x)⟩
  | smul c a _ h =>
    obtain ⟨a', ha, h⟩ := h
    exact ⟨c • a', Submodule.smul_mem _ c ha, fun x => by simp only [schr_smul]; exact (h x).const_mul c⟩

/- English proof (translation)
Take `⟨_, _, h⟩` from `exists_deriv hψ w hΦ`. Conclude with `(h x).differentiableAt.hasDerivAt`.
-/
theorem hasDerivAt_dR {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (x : κ → AF F) : HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (dR ψ w Φ x) 0 := by
  obtain ⟨_, _, h⟩ := exists_deriv hψ w hΦ
  exact (h x).differentiableAt.hasDerivAt

/- English proof (translation)
Take `⟨Φ', h1, h⟩` from `exists_deriv hψ w hΦ`. Rewrite using `[show dR ψ w Φ = Φ' from funext fun x => (h x).deriv]` and apply the resulting hypothesis.
-/
theorem dR_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    dR ψ w Φ ∈ schA F κ := by
  obtain ⟨Φ', h1, h⟩ := exists_deriv hψ w hΦ
  rwa [show dR ψ w Φ = Φ' from funext fun x => (h x).deriv]

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ w Φ hΦ`. Use `⟨dR_mem hψ w hΦ, hasDerivAt_dR hψ w hΦ, fun m hm u hu x => ?_⟩` and prove the remaining obligations. Unfold `dR`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Establish `e : ((m : AF F) • u) ⬝ᵥ (emb (t • w)).2 = 0` using `Finset.sum_eq_zero fun i _ => Prod.ext (by`. Express the relevant statement in the definitionally equal form `((m : AF F).1 * (u i).1) * _ = 0`. Rewrite using `[(hu i).1, mul_zero, zero_mul]) (by`. Express the relevant statement in the definitionally equal form `_ * (0 : Af F) = 0`. Rewrite using `[mul_zero])`.

Simplify using `only [schr]`. Rewrite using `[add_dotProduct, e, add_zero, add_right_comm, hm u hu]`.
-/
theorem derivOK : DerivOK := by
  intro F _ _ κ _ ψ hψ w Φ hΦ
  refine ⟨dR_mem hψ w hΦ, hasDerivAt_dR hψ w hΦ, fun m hm u hu x => ?_⟩
  unfold dR
  congr 1
  funext t
  have e : ((m : AF F) • u) ⬝ᵥ (emb (t • w)).2 = 0 := Finset.sum_eq_zero fun i _ => Prod.ext (by
    change ((m : AF F).1 * (u i).1) * _ = 0
    rw [(hu i).1, mul_zero, zero_mul]) (by
    change _ * (0 : Af F) = 0
    rw [mul_zero])
  simp only [schr]
  rw [add_dotProduct, e, add_zero, add_right_comm, hm u hu]

end PositivityTheory.ThKF0.Grow
