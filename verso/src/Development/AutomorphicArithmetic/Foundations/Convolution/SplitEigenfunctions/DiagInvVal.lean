import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal

/- English proof (translation)
Use `haveI := N.haar`. Use `haveI := N.right`. Establish `hm : ∀ s : (A E)ˣ, Measurable (cD s : G1 E → G1 E)` using `fun s => (M.continuous_cD s).measurable`. Set `e : G1 E ≃ₜ* G1 E` to `{ toFun := cD t invFun := cD t⁻¹ left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one] right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one] map_mul' := M.cD_mul t continuous_toFun := M.continuous_cD t continuous_invFun := M.continuous_cD t⁻¹ }`. Use `haveI : (N.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map N.μ`.

Take `⟨c, hc⟩ : ∃ c : ℝ≥0, N.μ.map (cD t) = c • N.μ` from `⟨_, Measure.isMulLeftInvariant_eq_smul (N.μ.map (cD t)) N.μ⟩`. Establish `h2 : N.μ.map (cD (t * t)) = N.μ`. Establish `: (cD (t * t) : G1 E → G1 E) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g)`. Use function extensionality and compare the values at `g`. Conclude with `M.cD_sq t g`.

Rewrite using `[this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self, map_mul_right_eq_self]`. Establish `h3 : N.μ.map (cD (t * t)) = (c * c) • N.μ`. Establish `: (cD (t * t) : G1 E → G1 E) = cD t ∘ cD t`. Use function extensionality and compare the values at `g`. Conclude with `(M.cD_cD t t g).symm`.

Rewrite using `[this, ← Measure.map_map (hm t) (hm t), hc, Measure.map_smul, hc, smul_smul]`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : G1 E)`. Establish `hpos : N.μ K ≠ 0` using `(Measure.measure_pos_of_mem_nhds N.μ hK1).ne'`. Establish `hfin : N.μ K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = N.μ K`.

Use `congrArg (fun m : Measure (G1 E) => m K) (h3.symm.trans h2)` as an intermediate fact. Simplify `this` using `[ENNReal.smul_def]`. Establish `h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1`. Establish `h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = 1 * N.μ K` using `by rw [h4, one_mul]`. Conclude with `(ENNReal.mul_left_inj hpos hfin).1 h6`.

Establish `h7 : c * c = 1` using `by exact_mod_cast h5`. Establish `h8 : c = 1`. Use `(mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)` as an intermediate fact. Break down `this with h | h` into its components or cases. Conclude with `h` after adjusting the coercions.

Use `c.coe_nonneg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hm t, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, h8, one_smul]`.
-/
private theorem cd_meas {E : Type} [Field E] [NumberField E] (N : MeasE E) (t : (A E)ˣ) :
    MeasurePreserving (cD t) N.μ N.μ := by
  haveI := N.haar
  haveI := N.right
  have hm : ∀ s : (A E)ˣ, Measurable (cD s : G1 E → G1 E) := fun s => (M.continuous_cD s).measurable
  let e : G1 E ≃ₜ* G1 E :=
    { toFun := cD t
      invFun := cD t⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      map_mul' := M.cD_mul t
      continuous_toFun := M.continuous_cD t
      continuous_invFun := M.continuous_cD t⁻¹ }
  haveI : (N.μ.map (cD t)).IsHaarMeasure := e.isHaarMeasure_map N.μ
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, N.μ.map (cD t) = c • N.μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (N.μ.map (cD t)) N.μ⟩
  have h2 : N.μ.map (cD (t * t)) = N.μ := by
    have : (cD (t * t) : G1 E → G1 E) = (fun g => g * mD t) ∘ (fun g => (mD t)⁻¹ * g) := by
      funext g; exact M.cD_sq t g
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
      map_mul_left_eq_self, map_mul_right_eq_self]
  have h3 : N.μ.map (cD (t * t)) = (c * c) • N.μ := by
    have : (cD (t * t) : G1 E → G1 E) = cD t ∘ cD t := by
      funext g; exact (M.cD_cD t t g).symm
    rw [this, ← Measure.map_map (hm t) (hm t), hc, Measure.map_smul, hc, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G1 E)
  have hpos : N.μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds N.μ hK1).ne'
  have hfin : N.μ K ≠ ∞ := hK.measure_lt_top.ne
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = N.μ K := by
    have := congrArg (fun m : Measure (G1 E) => m K) (h3.symm.trans h2)
    simpa [ENNReal.smul_def] using this
  have h5 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h6 : ((c * c : ℝ≥0) : ℝ≥0∞) * N.μ K = 1 * N.μ K := by rw [h4, one_mul]
    exact (ENNReal.mul_left_inj hpos hfin).1 h6
  have h7 : c * c = 1 := by exact_mod_cast h5
  have h8 : c = 1 := by
    have := (mul_self_eq_one_iff (a := (c : ℝ))).1 (by exact_mod_cast h7)
    rcases this with h | h
    · exact_mod_cast h
    · have := c.coe_nonneg; linarith
  refine ⟨hm t, ?_⟩
  rw [hc, h8, one_smul]

/- English proof (translation)
Use `haveI := N.haar`. Use `haveI := N.right`. Establish `hmp : MeasurePreserving (· * k) N.μ N.μ` using `measurePreserving_mul_right N.μ k`. Establish `hemb : MeasurableEmbedding (· * k : G1 E → G1 E)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `hfd : IsFundamentalDomain (Gam E) ((Equiv.mulRight k) '' N.D) N.μ`.

Use `N.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_` and prove the remaining obligations. Conclude with `(measurePreserving_mul_right N.μ k⁻¹).quasiMeasurePreserving`. Introduce `g x`. Simplify using `[Subgroup.smul_def, mul_assoc]`. Establish `hinv : ∀ (g : Gam E) x, u (g • x) = u x`.

Introduce and unpack `⟨_, γ, rfl⟩ x`. Simplify `hu γ x` using `[Subgroup.smul_def]`. Establish `hpre : (· * k : G1 E → G1 E) ⁻¹' ((Equiv.mulRight k) '' N.D) = N.D`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `h3` using `hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' N.D)`. Rewrite `h3` using `[hpre]`. Rewrite using `[h3]`. Conclude with `hfd.setIntegral_eq N.fund hinv`.
-/
private theorem right_tr {E : Type} [Field E] [NumberField E] (N : MeasE E) (u : G1 E → ℂ)
    (hu : ∀ γ g, u (ratS E γ * g) = u g) (k : G1 E) :
    ∫ g in N.D, u (g * k) ∂N.μ = ∫ g in N.D, u g ∂N.μ := by
  haveI := N.haar
  haveI := N.right
  have hmp : MeasurePreserving (· * k) N.μ N.μ := measurePreserving_mul_right N.μ k
  have hemb : MeasurableEmbedding (· * k : G1 E → G1 E) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam E) ((Equiv.mulRight k) '' N.D) N.μ := by
    refine N.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right N.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam E) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 E → G1 E) ⁻¹' ((Equiv.mulRight k) '' N.D) = N.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' N.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq N.fund hinv

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem diag_val (E : Type) [Field E] [NumberField E] (t : Eˣ) :
    ((IdeleGroup.diagonal E t : (A E)ˣ) : A E) = rt (t : E) := rfl

/- English proof (translation)
Rewrite using `[← map_inv, ← Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression.
-/
private theorem diag_inv_val (E : Type) [Field E] [NumberField E] (t : Eˣ) :
    (((IdeleGroup.diagonal E t : (A E)ˣ)⁻¹ : (A E)ˣ) : A E) = rt ((t : E)⁻¹) := by
  rw [← map_inv, ← Units.val_inv_eq_inv_val]
  rfl

private def cR {E : Type} [Field E] (t : Eˣ) (g : Matrix.SpecialLinearGroup (Fin 2) E) :
    Matrix.SpecialLinearGroup (Fin 2) E :=
  ⟨!![g 0 0, g 0 1 * (t : E)⁻¹; (t : E) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have ht : (t : E) ≠ 0 := t.ne_zero
    have : g 0 1 * (t : E)⁻¹ * ((t : E) * g 1 0) = g 0 1 * g 1 0 := by field_simp
    rw [this]
    exact h⟩

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[M.val_ratS]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[cD, cR, M.val_ratS, diag_inv_val, diag_val, UpperTheory.ConvolutionTheory.R2.rt, map_mul]`.
-/
private theorem cD_ratS {E : Type} [Field E] [NumberField E] (t : Eˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) E) :
    cD (IdeleGroup.diagonal E t) (ratS E g) = ratS E (cR t g) := by
  refine Subtype.ext ?_
  rw [M.val_ratS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cD, cR, M.val_ratS, diag_inv_val, diag_val, UpperTheory.ConvolutionTheory.R2.rt, map_mul]

/- English proof (translation)
Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨cR t g, (cD_ratS t g).symm⟩`.
-/
private theorem cD_mem {E : Type} [Field E] [NumberField E] (t : Eˣ) {x : G1 E} (hx : x ∈ Gam E) :
    cD (IdeleGroup.diagonal E t) x ∈ Gam E := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨cR t g, (cD_ratS t g).symm⟩

/- English proof (translation)
Use `haveI := N.haar`. Use `set T : (A E)ˣ := IdeleGroup.diagonal E t with hT`. Establish `hTi : T⁻¹ = IdeleGroup.diagonal E t⁻¹` using `by rw [hT, map_inv]`. Set `e : G1 E ≃ₜ G1 E` to `{ toFun := cD T invFun := cD T⁻¹ left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one] right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one] continuous_toFun := M.continuous_cD T continuous_invFun := M.continuous_cD T⁻¹ }`. Set `eG : Gam E ≃ Gam E` to `{ toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩ invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩ left_inv := fun γ => Subtype.ext (by show cD T (cD T⁻¹ γ.1) = γ.1`.

Rewrite using `[M.cD_cD, mul_inv_cancel, M.cD_one])`. Use `right_inv := fun γ => Subtype.ext (by show cD T⁻¹ (cD T γ.1) = γ.1`. Rewrite using `[M.cD_cD, inv_mul_cancel, M.cD_one]) }`. Establish `hmp : MeasurePreserving (cD T) N.μ N.μ` using `cd_meas N T`. Establish `hmpi : MeasurePreserving (cD T⁻¹) N.μ N.μ` using `cd_meas N T⁻¹`.

Establish `hemb : MeasurableEmbedding (cD T : G1 E → G1 E)` using `e.measurableEmbedding`. Establish `hD' : IsFundamentalDomain (Gam E) (cD T '' N.D) N.μ` using `N.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x`. Rewrite using `[M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])`. Establish `hpre : cD T ⁻¹' (cD T '' N.D) = N.D` using `Set.preimage_image_eq _ e.injective`. Establish `hinv : ∀ (γ : Gam E) (x : G1 E), u (γ • x) = u x`.

Introduce and unpack `⟨_, γ, rfl⟩ x`. Conclude with `hu γ x`. Establish `h1` using `hmp.setIntegral_preimage_emb hemb u (cD T '' N.D)`. Rewrite `h1` using `[hpre]`. Conclude with `h1.trans (hD'.setIntegral_eq N.fund hinv)`.
-/
private theorem conj_int {E : Type} [Field E] [NumberField E] (N : MeasE E) (u : G1 E → ℂ)
    (hu : ∀ γ g, u (ratS E γ * g) = u g) (t : Eˣ) :
    ∫ g in N.D, u (cD (IdeleGroup.diagonal E t) g) ∂N.μ = ∫ g in N.D, u g ∂N.μ := by
  haveI := N.haar
  set T : (A E)ˣ := IdeleGroup.diagonal E t with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal E t⁻¹ := by rw [hT, map_inv]
  let e : G1 E ≃ₜ G1 E :=
    { toFun := cD T
      invFun := cD T⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      continuous_toFun := M.continuous_cD T
      continuous_invFun := M.continuous_cD T⁻¹ }
  let eG : Gam E ≃ Gam E :=
    { toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩
      invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩
      left_inv := fun γ => Subtype.ext (by
        show cD T (cD T⁻¹ γ.1) = γ.1
        rw [M.cD_cD, mul_inv_cancel, M.cD_one])
      right_inv := fun γ => Subtype.ext (by
        show cD T⁻¹ (cD T γ.1) = γ.1
        rw [M.cD_cD, inv_mul_cancel, M.cD_one]) }
  have hmp : MeasurePreserving (cD T) N.μ N.μ := cd_meas N T
  have hmpi : MeasurePreserving (cD T⁻¹) N.μ N.μ := cd_meas N T⁻¹
  have hemb : MeasurableEmbedding (cD T : G1 E → G1 E) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (Gam E) (cD T '' N.D) N.μ :=
    N.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by
      show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x
      rw [M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])
  have hpre : cD T ⁻¹' (cD T '' N.D) = N.D := Set.preimage_image_eq _ e.injective
  have hinv : ∀ (γ : Gam E) (x : G1 E), u (γ • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    exact hu γ x
  have h1 := hmp.setIntegral_preimage_emb hemb u (cD T '' N.D)
  rw [hpre] at h1
  exact h1.trans (hD'.setIntegral_eq N.fund hinv)

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
private theorem glRat {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := Units.ext rfl

/- English proof (translation)
Establish `hm : gl (ratS E γ * g) = gl (ratS E γ) * gl g` using `map_mul _ _ _`. Rewrite using `[hm, glRat, mul_assoc]`. Conclude with `hΨ _ _`.
-/
private theorem linv {E : Type} [Field E] [NumberField E] {Ψ : GL (Fin 2) (A E) → ℂ} (hΨ : LRat Ψ)
    (y : GL (Fin 2) (A E)) (γ : Matrix.SpecialLinearGroup (Fin 2) E) (g : G1 E) :
    Ψ (gl (ratS E γ * g) * y) = Ψ (gl g * y) := by
  have hm : gl (ratS E γ * g) = gl (ratS E γ) * gl g := map_mul _ _ _
  rw [hm, glRat, mul_assoc]
  exact hΨ _ _

private def dR {E : Type} [Field E] (r : Eˣ) : GL (Fin 2) E :=
  ⟨!![1, 0; 0, (r : E)], !![1, 0; 0, ((r⁻¹ : Eˣ) : E)], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use `show (dR r).val.map (algebraMap E (A E)) = (dM (IdeleGroup.diagonal E r)).val`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dR, dM, diag_val, UpperTheory.ConvolutionTheory.R2.rt]`.
-/
private theorem ratGL_dR {E : Type} [Field E] [NumberField E] (r : Eˣ) :
    ratGL E 2 (dR r) = dM (IdeleGroup.diagonal E r) := by
  refine Units.ext ?_
  show (dR r).val.map (algebraMap E (A E)) = (dM (IdeleGroup.diagonal E r)).val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dR, dM, diag_val, UpperTheory.ConvolutionTheory.R2.rt]

/- English proof (translation)
Use `set r : Eˣ := Matrix.GeneralLinearGroup.det γ with hr`. Establish `hd : Matrix.GeneralLinearGroup.det (dR r) = r`. Use `Units.ext ?_` and prove the remaining obligations. Simplify using `[dR, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Establish `hdet : Matrix.GeneralLinearGroup.det ((dR r)⁻¹ * γ) = 1`.

Rewrite using `[map_mul, map_inv, hd, ← hr, inv_mul_cancel]`. Set `s : Matrix.SpecialLinearGroup (Fin 2) E` to `⟨((dR r)⁻¹ * γ).val, by`. Establish `h1` using `congrArg Units.val hdet`. Simplify `h1⟩` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hs : Matrix.SpecialLinearGroup.toGL s = (dR r)⁻¹ * γ` using `Units.ext rfl`.

Use `⟨r, s, ?_⟩` and prove the remaining obligations. Rewrite using `[glRat, hs, map_mul, ← ratGL_dR, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]`.
-/
private theorem rat_decomp {E : Type} [Field E] [NumberField E] (γ : GL (Fin 2) E) :
    ∃ (r : Eˣ) (s : Matrix.SpecialLinearGroup (Fin 2) E),
      ratGL E 2 γ = dM (IdeleGroup.diagonal E r) * gl (ratS E s) := by
  set r : Eˣ := Matrix.GeneralLinearGroup.det γ with hr
  have hd : Matrix.GeneralLinearGroup.det (dR r) = r := by
    refine Units.ext ?_
    simp [dR, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dR r)⁻¹ * γ) = 1 := by
    rw [map_mul, map_inv, hd, ← hr, inv_mul_cancel]
  let s : Matrix.SpecialLinearGroup (Fin 2) E := ⟨((dR r)⁻¹ * γ).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = (dR r)⁻¹ * γ := Units.ext rfl
  refine ⟨r, s, ?_⟩
  rw [glRat, hs, map_mul, ← ratGL_dR, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

/- English proof (translation)
Introduce `E _ _ N`. Use `⟨cd_meas N, fun Ψ hΨ => ?_⟩` and prove the remaining obligations. Establish `hright : ∀ h : G1 E, (mean N fun x => Ψ (x * gl h)) = mean N Ψ`. Introduce `h`. Unfold `mean`.

Establish `e : ∀ x : G1 E, Ψ (gl x * gl h) = Ψ (gl (x * h))` using `fun x => by`. Establish `hm : gl (x * h) = gl x * gl h` using `map_mul _ _ _`. Rewrite using `[hm]`. Simplify using `only [e]`. Use `right_tr N (fun x => Ψ (gl x)) (fun γ g => ?_) h` and prove the remaining obligations.

Simplify using `using linv hΨ 1 γ g`. Use `⟨hright, fun γ => ?_⟩` and prove the remaining obligations. Take `⟨r, s, hγ⟩` from `rat_decomp γ`. Use `set S : GL (Fin 2) (A E) := gl (ratS E s) with hS`. Use `set T : (A E)ˣ := IdeleGroup.diagonal E r with hT`.

Establish `hTi : T⁻¹ = IdeleGroup.diagonal E r⁻¹` using `by rw [hT, map_inv]`. Establish `e : ∀ x : G1 E, Ψ (gl x * ratGL E 2 γ) = Ψ (gl (cD (IdeleGroup.diagonal E r⁻¹) x) * S)`. Introduce `x`. Establish `h1 : gl x * dM T = dM T * gl (cD T⁻¹ x)`. Use `M.gl_cD T (cD T⁻¹ x)` as an intermediate fact.

Rewrite `this` using `[M.cD_cD, mul_inv_cancel, M.cD_one]`. Then use the resulting hypothesis. Rewrite using `[hγ, ← mul_assoc, h1, mul_assoc, hT, ← ratGL_dR, hΨ, ← hT, hTi]`. Establish `h2 : (mean N fun x => Ψ (x * ratGL E 2 γ)) = ∫ x in N.D, Ψ (gl x * S) ∂N.μ`. Unfold `mean`. Simplify using `only [e]`.

Conclude with `conj_int N (fun x => Ψ (gl x * S)) (fun γ' g => linv hΨ S γ' g) r⁻¹`. Rewrite using `[h2]`. Conclude with `hright (ratS E s)`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.invE :
    InvE := by
  intro E _ _ N
  refine ⟨cd_meas N, fun Ψ hΨ => ?_⟩
  have hright : ∀ h : G1 E, (mean N fun x => Ψ (x * gl h)) = mean N Ψ := by
    intro h
    unfold mean
    have e : ∀ x : G1 E, Ψ (gl x * gl h) = Ψ (gl (x * h)) := fun x => by
      have hm : gl (x * h) = gl x * gl h := map_mul _ _ _
      rw [hm]
    simp only [e]
    refine right_tr N (fun x => Ψ (gl x)) (fun γ g => ?_) h
    simpa using linv hΨ 1 γ g
  refine ⟨hright, fun γ => ?_⟩
  obtain ⟨r, s, hγ⟩ := rat_decomp γ
  set S : GL (Fin 2) (A E) := gl (ratS E s) with hS
  set T : (A E)ˣ := IdeleGroup.diagonal E r with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal E r⁻¹ := by rw [hT, map_inv]
  have e : ∀ x : G1 E, Ψ (gl x * ratGL E 2 γ) = Ψ (gl (cD (IdeleGroup.diagonal E r⁻¹) x) * S) := by
    intro x
    have h1 : gl x * dM T = dM T * gl (cD T⁻¹ x) := by
      have := M.gl_cD T (cD T⁻¹ x)
      rwa [M.cD_cD, mul_inv_cancel, M.cD_one] at this
    rw [hγ, ← mul_assoc, h1, mul_assoc, hT, ← ratGL_dR, hΨ, ← hT, hTi]
  have h2 : (mean N fun x => Ψ (x * ratGL E 2 γ)) =
      ∫ x in N.D, Ψ (gl x * S) ∂N.μ := by
    unfold mean
    simp only [e]
    exact conj_int N (fun x => Ψ (gl x * S)) (fun γ' g => linv hΨ S γ' g) r⁻¹
  rw [h2]
  exact hright (ratS E s)
