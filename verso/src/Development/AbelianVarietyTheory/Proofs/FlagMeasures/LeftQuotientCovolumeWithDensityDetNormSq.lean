import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.DetSlab

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

/- English proof (translation)
Unfold `detNorm`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `: Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w)` using `rfl`. Rewrite using `[this, Matrix.det_mul, norm_mul, mul_pow]`.
-/
theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [this, Matrix.det_mul, norm_mul, mul_pow]

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => sq_nonneg _`.
-/
theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

/- English proof (translation)
Take `⟨γ, hγ, hx⟩` from `hx`. Establish `h1 : IsIntegral ℤ (γ : Matrix (Fin j) (Fin j) E).det` using `GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ v).2 hv`. Establish `h2 : IsIntegral ℤ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det` using `GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ _).1 (by`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Conclude with `hv)`.

Establish `h3 : (γ : Matrix (Fin j) (Fin j) E).det * ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det = 1`. Rewrite using `[← Matrix.det_mul, Units.mul_inv, Matrix.det_one]`. Set `u : (𝓞 E)ˣ` to `Units.mkOfMulEqOne ⟨_, h1⟩ ⟨_, h2⟩ (RingOfIntegers.ext h3)`. Establish `h4` using `InfinitePlace.prod_eq_abs_norm ((u : 𝓞 E) : E)`. Rewrite `h4` using `[NumberField.Units.norm]`.

Establish `hu : ((u : 𝓞 E) : E) = (γ : Matrix (Fin j) (Fin j) E).det` using `rfl`. Rewrite `h4` using `[hu]`. Unfold `detNorm`. Rewrite `h4` using `[Rat.cast_one]`. Rewrite using `[← h4]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `h5 : Matrix.of (x w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E)`. Use extensionality with `a b`. Simplify using `using hx w a b`. Rewrite using `[h5, ← RingHom.map_det, InfinitePlace.norm_embedding_eq, (IsTotallyComplex.isComplex w).mult_eq_two]`.
-/
theorem detNorm_aut (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ)
    {x : MatInf E j} (hx : x ∈ autGL E j Λ) : detNorm E j x = 1 := by
  obtain ⟨γ, hγ, hx⟩ := hx
  have h1 : IsIntegral ℤ (γ : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ v).2 hv
  have h2 : IsIntegral ℤ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ _).1 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hv)
  have h3 : (γ : Matrix (Fin j) (Fin j) E).det * ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne ⟨_, h1⟩ ⟨_, h2⟩ (RingOfIntegers.ext h3)
  have h4 := InfinitePlace.prod_eq_abs_norm ((u : 𝓞 E) : E)
  rw [NumberField.Units.norm] at h4
  have hu : ((u : 𝓞 E) : E) = (γ : Matrix (Fin j) (Fin j) E).det := rfl
  rw [hu] at h4
  unfold detNorm
  rw [Rat.cast_one] at h4
  rw [← h4]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h5 : Matrix.of (x w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := by
    ext a b
    simpa using hx w a b
  rw [h5, ← RingHom.map_det, InfinitePlace.norm_embedding_eq, (IsTotallyComplex.isComplex w).mult_eq_two]

/- English proof (translation)
Unfold `detNorm`. Use `continuous_finset_prod _ fun w _ => ?_` and prove the remaining obligations. Use `(Continuous.norm ?_).pow 2` and prove the remaining obligations. Conclude with `Continuous.matrix_det (continuous_apply w)`.
-/
theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finset_prod _ fun w _ => ?_
  refine (Continuous.norm ?_).pow 2
  exact Continuous.matrix_det (continuous_apply w)

/- English proof (translation)
The claim follows from `(continuous_detNorm E j).measurable`.
-/
theorem measurable_detNorm : Measurable (detNorm E j) := (continuous_detNorm E j).measurable

def scal (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scal_eq (t : ℝ) (x : InfinitePlace E → Fin j → Fin j → ℂ) : scal E j t x = t • x := rfl

/- English proof (translation)
The claim follows from `(continuous_const_smul t : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => t • x).measurable`.
-/
theorem measurable_scal (t : ℝ) : Measurable (scal E j t) :=
  (continuous_const_smul t : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => t • x).measurable

/- English proof (translation)
Unfold `detNorm`. Establish `: ∀ w, Matrix.of (scal E j t x w) = (t : ℂ) • Matrix.of (x w)` using `fun w => rfl`. Simplify using `only [this, Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, Finset.card_univ, ← pow_mul]`. Rewrite using `[mul_comm j 2]`.
-/
theorem detNorm_scal (t : ℝ) (x : MatInf E j) :
    detNorm E j (scal E j t x) = |t| ^ (2 * j * Fintype.card (InfinitePlace E)) * detNorm E j x := by
  unfold detNorm
  have : ∀ w, Matrix.of (scal E j t x w) = (t : ℂ) • Matrix.of (x w) := fun w => rfl
  simp only [this, Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, Finset.card_univ, ← pow_mul]
  rw [mul_comm j 2]

/- English proof (translation)
Use `haveI h1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI h2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

/- English proof (translation)
Establish `hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)` using `(((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal`. Establish `hf' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f x)` using `hf`. Establish `hf'' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f (t • x))` using `hf.comp (measurable_scal E j t)`. Establish `e1` using `lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf'`. Establish `e2` using `lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf''`.

Use `e2.trans (Eq.trans ?_ e1.symm)` and prove the remaining obligations. Use `haveI := isAddHaar_volume E j`. Establish `hm` using `Measure.map_addHaar_smul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) ht`. Establish `hrk : Module.finrank ℝ (InfinitePlace E → Fin j → Fin j → ℂ) = 2 * j * Fintype.card (InfinitePlace E) * j`. Simplify using `only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3` using `lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (hd.mul hf') (measurable_const_smul t)`. Rewrite `e3` using `[hm, lintegral_smul_measure, hrk, smul_eq_mul]`. Use `set N := 2 * j * Fintype.card (InfinitePlace E) with hN`. Establish `hpos : 0 < |t| ^ (N * j)` using `pow_pos (abs_pos.2 ht) _`.

Establish `e4 : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ, ENNReal.ofReal ((detNorm E j (t • x))⁻¹ ^ j) = ENNReal.ofReal |(t ^ (N * j))⁻¹| * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)`. Introduce `x`. Establish `h : detNorm E j (t • x) = |t| ^ N * detNorm E j x` using `detNorm_scal E j t x`. Rewrite using `[← ENNReal.ofReal_mul (abs_nonneg _), h, abs_inv, abs_pow, mul_inv, mul_pow, inv_pow, ← pow_mul]`. Establish `e5` using `lintegral_const_mul (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (ENNReal.ofReal |(t ^ (N * j))⁻¹|) (hd.mul hf'')`.

Use `replace e3 := e3.trans ((lintegral_congr fun x => (congrArg (· * f (scal E j t x)) (e4 x)).trans (mul_assoc _ _ _)).trans e5)`. Establish `hne : ENNReal.ofReal |(t ^ (N * j))⁻¹| ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le, abs_inv, abs_pow]`. Conclude with `inv_pos.2 hpos`. Conclude with `((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 e3).symm`.
-/
theorem lintegral_scal (t : ℝ) (ht : t ≠ 0) (f : MatInf E j → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (scal E j t x) ∂(haarGL E j) = ∫⁻ x, f x ∂(haarGL E j) := by
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  have hf' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f x) := hf
  have hf'' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f (t • x)) :=
    hf.comp (measurable_scal E j t)
  have e1 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf'
  have e2 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf''
  refine e2.trans (Eq.trans ?_ e1.symm)
  haveI := isAddHaar_volume E j
  have hm := Measure.map_addHaar_smul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) ht
  have hrk : Module.finrank ℝ (InfinitePlace E → Fin j → Fin j → ℂ) =
      2 * j * Fintype.card (InfinitePlace E) * j := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have e3 := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (hd.mul hf')
    (measurable_const_smul t)
  rw [hm, lintegral_smul_measure, hrk, smul_eq_mul] at e3
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hpos : 0 < |t| ^ (N * j) := pow_pos (abs_pos.2 ht) _
  have e4 : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ, ENNReal.ofReal ((detNorm E j (t • x))⁻¹ ^ j) =
      ENNReal.ofReal |(t ^ (N * j))⁻¹| * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have h : detNorm E j (t • x) = |t| ^ N * detNorm E j x := detNorm_scal E j t x
    rw [← ENNReal.ofReal_mul (abs_nonneg _), h, abs_inv, abs_pow, mul_inv, mul_pow,
      inv_pow, ← pow_mul]
  have e5 := lintegral_const_mul (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
    (ENNReal.ofReal |(t ^ (N * j))⁻¹|) (hd.mul hf'')
  replace e3 := e3.trans ((lintegral_congr fun x => (congrArg (· * f (scal E j t x)) (e4 x)).trans
    (mul_assoc _ _ _)).trans e5)
  have hne : ENNReal.ofReal |(t ^ (N * j))⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_inv, abs_pow]; exact inv_pos.2 hpos
  exact ((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 e3).symm

/- English proof (translation)
Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Establish `hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)` using `(((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal`. Use `(ae_withDensity_iff hd).2 (Filter.Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Use `lt_of_le_of_ne (detNorm_nonneg E j x) fun h => hx ?_` and prove the remaining obligations. Rewrite using `[← h, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]`.
-/
theorem restrict_pos (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  refine (ae_withDensity_iff hd).2 (Filter.Eventually.of_forall fun x hx => ?_)
  refine lt_of_le_of_ne (detNorm_nonneg E j x) fun h => hx ?_
  rw [← h, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]

/- English proof (translation)
Use `haveI := isAddHaar_volume E j`. Conclude with `(Measure.withDensity.instSFinite : SFinite (Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) _))`.
-/
theorem sFinite_haarGL : SFinite (haarGL E j) := by
  haveI := isAddHaar_volume E j
  exact (Measure.withDensity.instSFinite :
    SFinite (Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) _))

/- English proof (translation)
Establish `h` using `lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn (fun t => F t / ENNReal.ofReal t)`. Rewrite `h` using `[Set.image_univ, Real.range_exp, Measure.restrict_univ]`. Rewrite using `[h]`. Use `lintegral_congr fun u => ?_` and prove the remaining obligations. Rewrite using `[abs_of_pos (Real.exp_pos u), ENNReal.mul_div_cancel (by simpa using Real.exp_pos u) ENNReal.ofReal_ne_top]`.
-/
theorem lintegral_exp (F : ℝ → ENNReal) :
    ∫⁻ u, F (Real.exp u) = ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => F t / ENNReal.ofReal t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun u => ?_
  rw [abs_of_pos (Real.exp_pos u), ENNReal.mul_div_cancel
    (by simpa using Real.exp_pos u) ENNReal.ofReal_ne_top]

/- English proof (translation)
Use `haveI := sFinite_haarGL E j`. Establish `hl : Measurable fun g => Real.log (detNorm E j g)` using `Real.measurable_log.comp (measurable_detNorm E j)`. Use `set ν : Measure ℝ := ((haarGL E j).restrict D).map fun g => Real.log (detNorm E j g) with hν`. Establish `hνa : ∀ s, MeasurableSet s → ν s = haarGL E j ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D)` using `fun s hs => by rw [hν, Measure.map_apply hl hs, Measure.restrict_apply (hl hs)]`. Use `set N := 2 * j * Fintype.card (InfinitePlace E) with hN`.

Establish `hN0 : (N : ℝ) ≠ 0`. Establish `: 0 < N` using `Nat.mul_pos (by omega) Fintype.card_pos`. Conclude with `this.ne'` after adjusting the coercions. Use `haveI : ν.IsAddLeftInvariant := by`. Use `⟨fun c => ?_⟩` and prove the remaining obligations.

Use extensionality with `s hs`. Establish `hc : Measurable fun u : ℝ => c + u` using `measurable_const_add c`. Rewrite using `[Measure.map_apply hc hs, hνa _ (hc hs), hνa _ hs]`. Establish `hA : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D)` using `(hl hs).inter hD`. Establish `hB : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' ((fun u => c + u) ⁻¹' s) ∩ D)` using `(hl (hc hs)).inter hD`.

Establish `ht : 0 < Real.exp (c / N)` using `Real.exp_pos _`. Rewrite using `[← lintegral_indicator_one hA, ← lintegral_indicator_one hB, ← lintegral_scal E j _ ht.ne' _ (measurable_one.indicator hA)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hback : scal E j (Real.exp (c / N))⁻¹ (scal E j (Real.exp (c / N)) x) = x`. Use function extensionality and compare the values at `w a b`.

Simplify using `only [scal]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]`. Establish `hlog : x ∈ D → Real.log (detNorm E j (scal E j (Real.exp (c / N)) x)) = c + Real.log (detNorm E j x)` using `fun hx => by`. Establish `h0 : 0 < detNorm E j x` using `hpos hx`. Rewrite using `[detNorm_scal, abs_of_pos ht, Real.log_mul (pow_pos ht _).ne' h0.ne', Real.log_pow, Real.log_exp, ← hN, mul_div_cancel₀ _ hN0]`.

Use `(Set.indicator_const_eq_indicator_const (c := (1 : ENNReal)) ⟨fun h => ⟨?_, hsc _ h.2 _ ht⟩, fun h => ?_⟩)` and prove the remaining obligations. Use `h.1` as an intermediate fact. Simplify using `only [Set.mem_preimage] at this ⊢`. Rewrite using `[hlog h.2]` and apply the resulting hypothesis. Establish `hx : x ∈ D` using `hback ▸ hsc _ h.2 _ (inv_pos.2 ht)`.

Use `⟨?_, hx⟩` and prove the remaining obligations. Use `h.1` as an intermediate fact. Simplify using `only [Set.mem_preimage] at this ⊢`. Rewrite `this` using `[hlog hx]`. Then use the resulting hypothesis. Establish `hv : (volume : Measure ℝ) (Set.Ico 0 1) = 1` using `by simp`.

Establish `hFe : Measurable fun u => F (Real.exp u)` using `hF.comp Real.measurable_exp`. Establish `h1` using `measure_add_lintegral_eq volume ν (s := Set.Ico 0 1) measurableSet_Ico _ hFe`. Simplify using `only [measure_preimage_add_right] at h1`. Rewrite `h1` using `[hv, one_mul, lintegral_const_mul _ (f := fun u => F (Real.exp (-u))) (hFe.comp measurable_neg), lintegral_neg_eq_self (fun u => F (Real.exp u)), hνa _ measurableSet_Ico]`. Establish `hset : (fun g => Real.log (detNorm E j g)) ⁻¹' Set.Ico 0 1 ∩ D = {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D`.

Use extensionality with `x`. Use `and_congr_left fun hx => ?_` and prove the remaining obligations. Establish `h0 : 0 < detNorm E j x` using `hpos hx`. Simplify using `only [Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]`. Rewrite using `[Real.log_nonneg_iff h0, Real.log_lt_iff_lt_exp h0]`.

Rewrite `h1` using `[hset]`. Establish `h2 : ∫⁻ u, F (Real.exp u) ∂ν = ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j)`. Rewrite using `[hν, lintegral_map hFe hl]`. Use `setLIntegral_congr_fun hD fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Real.exp_log (hpos hx)]`.

Rewrite using `[← h2, h1, lintegral_exp]`.
-/
theorem lintegral_cone (hj : 1 ≤ j) (D : Set (MatInf E j)) (hD : MeasurableSet D)
    (hpos : D ⊆ {g | 0 < detNorm E j g}) (hsc : ∀ g ∈ D, ∀ t : ℝ, 0 < t → scal E j t g ∈ D)
    (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) =
      haarGL E j ({x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D) *
        ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  haveI := sFinite_haarGL E j
  have hl : Measurable fun g => Real.log (detNorm E j g) := Real.measurable_log.comp (measurable_detNorm E j)
  set ν : Measure ℝ := ((haarGL E j).restrict D).map fun g => Real.log (detNorm E j g) with hν
  have hνa : ∀ s, MeasurableSet s → ν s = haarGL E j ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) :=
    fun s hs => by rw [hν, Measure.map_apply hl hs, Measure.restrict_apply (hl hs)]
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 0 < N := Nat.mul_pos (by omega) Fintype.card_pos
    exact_mod_cast this.ne'
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext s hs
    have hc : Measurable fun u : ℝ => c + u := measurable_const_add c
    rw [Measure.map_apply hc hs, hνa _ (hc hs), hνa _ hs]
    have hA : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) := (hl hs).inter hD
    have hB : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' ((fun u => c + u) ⁻¹' s) ∩ D) :=
      (hl (hc hs)).inter hD
    have ht : 0 < Real.exp (c / N) := Real.exp_pos _
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hB,
      ← lintegral_scal E j _ ht.ne' _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hback : scal E j (Real.exp (c / N))⁻¹ (scal E j (Real.exp (c / N)) x) = x := by
      funext w a b
      simp only [scal]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
    have hlog : x ∈ D → Real.log (detNorm E j (scal E j (Real.exp (c / N)) x)) =
        c + Real.log (detNorm E j x) := fun hx => by
      have h0 : 0 < detNorm E j x := hpos hx
      rw [detNorm_scal, abs_of_pos ht, Real.log_mul (pow_pos ht _).ne' h0.ne', Real.log_pow, Real.log_exp, ← hN,
        mul_div_cancel₀ _ hN0]
    refine (Set.indicator_const_eq_indicator_const (c := (1 : ENNReal)) ⟨fun h => ⟨?_, hsc _ h.2 _ ht⟩, fun h => ?_⟩)
    · have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog h.2]
    · have hx : x ∈ D := hback ▸ hsc _ h.2 _ (inv_pos.2 ht)
      refine ⟨?_, hx⟩
      have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog hx] at this
  have hv : (volume : Measure ℝ) (Set.Ico 0 1) = 1 := by simp
  have hFe : Measurable fun u => F (Real.exp u) := hF.comp Real.measurable_exp
  have h1 := measure_add_lintegral_eq volume ν (s := Set.Ico 0 1) measurableSet_Ico _ hFe
  simp only [measure_preimage_add_right] at h1
  rw [hv, one_mul, lintegral_const_mul _ (f := fun u => F (Real.exp (-u))) (hFe.comp measurable_neg), lintegral_neg_eq_self (fun u => F (Real.exp u)),
    hνa _ measurableSet_Ico] at h1
  have hset : (fun g => Real.log (detNorm E j g)) ⁻¹' Set.Ico 0 1 ∩ D =
      {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D := by
    ext x
    refine and_congr_left fun hx => ?_
    have h0 : 0 < detNorm E j x := hpos hx
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    rw [Real.log_nonneg_iff h0, Real.log_lt_iff_lt_exp h0]
  rw [hset] at h1
  have h2 : ∫⁻ u, F (Real.exp u) ∂ν = ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) := by
    rw [hν, lintegral_map hFe hl]
    refine setLIntegral_congr_fun hD fun x hx => ?_
    simp only [Real.exp_log (hpos hx)]
  rw [← h2, h1, lintegral_exp]

/- English proof (translation)
Introduce `E _ _ hE j hj Λ hΛ F hF`. Take `⟨D, hD, hpos, -, hsc, hcov⟩` from `GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ`. Establish `hm` using `measurable_detNorm E j`. Establish `hP : MeasurableSet {g : MatInf E j | 0 < detNorm E j g}` using `measurableSet_lt measurable_const hm`. Establish `hS : MeasurableSet {x : MatInf E j | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}` using `(measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)`.

Establish `hinv : ∀ γ ∈ autGL E j Λ, ∀ g, detNorm E j (γ * g) = detNorm E j g` using `fun γ hγ g => by`. Rewrite using `[detNorm_mul, detNorm_aut E j hE Λ hΛ hγ, one_mul]`. Establish `h1` using `hcov (fun x => F (detNorm E j x)) _ ((hF.comp hm).indicator hP) (fun γ hγ g _ => by simp only [hinv γ hγ g]) hP subset_rfl (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)`. Establish `h2` using `hcov (fun _ => 1) _ (measurable_const.indicator hP) (fun _ _ _ _ => rfl) hS (fun g hg => lt_of_lt_of_le one_pos hg.1) (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)`. Rewrite `h1`, `h2` using `[restrict_pos E j hj]`.

Rewrite `h2` using `[withDensity_const, one_smul, setLIntegral_one]`. Rewrite using `[h1, h2, Set.inter_eq_right.2 hpos]`. Conclude with `lintegral_cone E j hj D hD hpos hsc F hF`.
-/
theorem covol_withDensity_detNorm : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  obtain ⟨D, hD, hpos, -, hsc, hcov⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  have hm := measurable_detNorm E j
  have hP : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {x : MatInf E j | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} :=
    (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hinv : ∀ γ ∈ autGL E j Λ, ∀ g, detNorm E j (γ * g) = detNorm E j g := fun γ hγ g => by
    rw [detNorm_mul, detNorm_aut E j hE Λ hΛ hγ, one_mul]
  have h1 := hcov (fun x => F (detNorm E j x)) _ ((hF.comp hm).indicator hP)
    (fun γ hγ g _ => by simp only [hinv γ hγ g]) hP subset_rfl
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  have h2 := hcov (fun _ => 1) _ (measurable_const.indicator hP) (fun _ _ _ _ => rfl) hS
    (fun g hg => lt_of_lt_of_le one_pos hg.1)
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  rw [restrict_pos E j hj] at h1 h2
  rw [withDensity_const, one_smul, setLIntegral_one] at h2
  rw [h1, h2, Set.inter_eq_right.2 hpos]
  exact lintegral_cone E j hj D hD hpos hsc F hF

end GlobalTheory.DetSlab
