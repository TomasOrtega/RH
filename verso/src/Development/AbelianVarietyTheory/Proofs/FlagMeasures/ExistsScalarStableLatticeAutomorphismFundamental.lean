import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatDom

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_mul (x y : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl

/- English proof (translation)
The claim follows from `funext fun w => Matrix.of.injective (h w)`.
-/
theorem matInf_ext {x y : MatInf E j} (h : ∀ w, Matrix.of (x w) = Matrix.of (y w)) : x = y :=
  funext fun w => Matrix.of.injective (h w)

/- English proof (translation)
Unfold `detNorm`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[of_mul, Matrix.det_mul, norm_mul, mul_pow]`.
-/
theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [of_mul, Matrix.det_mul, norm_mul, mul_pow]

/- English proof (translation)
Unfold `detNorm`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Rewrite `h` using `[Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])]`. Conclude with `lt_irrefl _ h`.

Introduce `h`. Conclude with `Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2`.
-/
theorem detNorm_pos_iff (x : MatInf E j) : 0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

/- English proof (translation)
Unfold `detNorm`. Use `continuous_finset_prod _ fun w _ => ?_` and prove the remaining obligations. Use `(Continuous.norm ?_).pow 2` and prove the remaining obligations. Conclude with `Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w)) (continuous_apply w)`.
-/
theorem continuous_detNorm :
    Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x := by
  unfold detNorm
  refine continuous_finset_prod _ fun w _ => ?_
  refine (Continuous.norm ?_).pow 2
  exact Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
    (continuous_apply w)

/- English proof (translation)
The claim follows from `continuous_detNorm.measurable`.
-/
theorem measurable_detNorm : Measurable (detNorm E j) := continuous_detNorm.measurable

def mulLin (γ : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℂ] (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun x := fun w a b => ∑ c, γ w a c * x w c b
  map_add' x y := by
    funext w a b
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    funext w a b
    simp [Finset.mul_sum, mul_left_comm]

def reidx (E : Type) [Field E] (j : ℕ) :
    (InfinitePlace E → Fin j → Fin j → ℂ) ≃ₗ[ℂ] (Fin j × (InfinitePlace E × Fin j) → ℂ) where
  toFun x := fun p => x p.2.1 p.1 p.2.2
  invFun y := fun w a b => y (a, (w, b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Establish `h : (reidx E j : _ →ₗ[ℂ] _) ∘ₗ mulLin γ ∘ₗ ((reidx E j).symm : _ →ₗ[ℂ] _) = Matrix.toLin' (Matrix.blockDiagonal fun p : InfinitePlace E × Fin j => Matrix.of (γ p.1))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Use function extensionality and compare the values at `⟨a, w, b⟩`. Rewrite using `[Matrix.toLin'_apply]`.

Express the relevant statement in the definitionally equal form `∑ c, γ w a c * y (c, (w, b)) = _`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `[ite_mul]`.

Rewrite using `[← LinearMap.det_conj (mulLin γ) (reidx E j), h, LinearMap.det_toLin', Matrix.det_blockDiagonal, Fintype.prod_prod_type, ← Finset.prod_pow]`. Simplify using the standard rewrite rules.
-/
theorem det_mulLin (γ : MatInf E j) :
    LinearMap.det (mulLin γ) = (∏ w, (Matrix.of (γ w)).det) ^ j := by
  classical
  have h : (reidx E j : _ →ₗ[ℂ] _) ∘ₗ mulLin γ ∘ₗ ((reidx E j).symm : _ →ₗ[ℂ] _) =
      Matrix.toLin' (Matrix.blockDiagonal fun p : InfinitePlace E × Fin j => Matrix.of (γ p.1)) := by
    apply LinearMap.ext
    intro y
    funext ⟨a, w, b⟩
    rw [Matrix.toLin'_apply]
    change ∑ c, γ w a c * y (c, (w, b)) = _
    simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ite_mul]
  rw [← LinearMap.det_conj (mulLin γ) (reidx E j), h, LinearMap.det_toLin', Matrix.det_blockDiagonal,
    Fintype.prod_prod_type, ← Finset.prod_pow]
  simp

/- English proof (translation)
Rewrite using `[LinearMap.det_restrictScalars, det_mulLin, Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]`. Both sides reduce to the same expression.
-/
theorem det_mulLin_real (γ : MatInf E j) :
    LinearMap.det ((mulLin γ).restrictScalars ℝ) = detNorm E j γ ^ j := by
  rw [LinearMap.det_restrictScalars, det_mulLin, Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq,
    norm_prod, ← Finset.prod_pow]
  rfl

/- English proof (translation)
The claim follows from `(mulLin γ).continuous_of_finiteDimensional.measurable`.
-/
theorem measurable_mul_left (γ : MatInf E j) : Measurable fun x : MatInf E j => γ * x :=
  (mulLin γ).continuous_of_finiteDimensional.measurable

/- English proof (translation)
The claim follows from `(measurable_detNorm.inv.pow_const j).ennreal_ofReal`.
-/
theorem measurable_dens :
    Measurable fun x : MatInf E j => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
  (measurable_detNorm.inv.pow_const j).ennreal_ofReal

/- English proof (translation)
Establish `hd : 0 < detNorm E j γ ^ j` using `pow_pos hγ j`. Use `haveI i1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI i2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI i3 : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `hmap` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) (f := (mulLin γ).restrictScalars ℝ) (by rw [det_mulLin_real]; exact hd.ne')`.

Rewrite `hmap` using `[det_mulLin_real, abs_of_pos (inv_pos.2 hd)]`. Set `vol : Measure (MatInf E j)` to `(volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))`. Use `set ρ : MatInf E j → ENNReal := fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) with hρ`. Establish `hρm : Measurable ρ` using `measurable_dens`. Establish `h1 : ∀ F : MatInf E j → ENNReal, Measurable F → ∫⁻ x, F x ∂(haarGL E j) = ∫⁻ x, ρ x * F x ∂vol` using `fun F hF => lintegral_withDensity_eq_lintegral_mul _ hρm hF`.

Establish `h2 : ∀ x, ρ x = ENNReal.ofReal (detNorm E j γ ^ j) * ρ (γ * x)`. Introduce `x`. Simplify using `only [hρ]`. Rewrite using `[← ENNReal.ofReal_mul hd.le, detNorm_mul, ← mul_pow, mul_inv, mul_inv_cancel_left₀ hγ.ne']`. Rewrite using `[h1 (fun x => F (γ * x)) (hF.comp (measurable_mul_left γ)), h1 _ hF]`.

Establish `h3 : ∫⁻ x, ρ (γ * x) * F (γ * x) ∂vol = ENNReal.ofReal (detNorm E j γ ^ j)⁻¹ * ∫⁻ x, ρ x * F x ∂vol`. Use `lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (f := fun x : InfinitePlace E → Fin j → Fin j → ℂ => ρ x * F x) (g := (mulLin γ).restrictScalars ℝ) (hρm.mul hF) (measurable_mul_left γ)` as an intermediate fact. Rewrite `this` using `[hmap, lintegral_smul_measure]`. Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← h2]`. Use `_ = _ := by`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3, ← mul_assoc, ← ENNReal.ofReal_mul hd.le, mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one, one_mul]`.
-/
theorem lintegral_haarGL_mul_left (γ : MatInf E j) (hγ : 0 < detNorm E j γ) (F : MatInf E j → ENNReal)
    (hF : Measurable F) : ∫⁻ x, F (γ * x) ∂(haarGL E j) = ∫⁻ x, F x ∂(haarGL E j) := by
  have hd : 0 < detNorm E j γ ^ j := pow_pos hγ j
  haveI i1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) (f := (mulLin γ).restrictScalars ℝ)
    (by rw [det_mulLin_real]; exact hd.ne')
  rw [det_mulLin_real, abs_of_pos (inv_pos.2 hd)] at hmap
  let vol : Measure (MatInf E j) := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
  set ρ : MatInf E j → ENNReal := fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) with hρ
  have hρm : Measurable ρ := measurable_dens
  have h1 : ∀ F : MatInf E j → ENNReal, Measurable F → ∫⁻ x, F x ∂(haarGL E j) =
      ∫⁻ x, ρ x * F x ∂vol := fun F hF =>
    lintegral_withDensity_eq_lintegral_mul _ hρm hF
  have h2 : ∀ x, ρ x = ENNReal.ofReal (detNorm E j γ ^ j) * ρ (γ * x) := by
    intro x
    simp only [hρ]
    rw [← ENNReal.ofReal_mul hd.le, detNorm_mul, ← mul_pow, mul_inv, mul_inv_cancel_left₀ hγ.ne']
  rw [h1 (fun x => F (γ * x)) (hF.comp (measurable_mul_left γ)), h1 _ hF]
  have h3 : ∫⁻ x, ρ (γ * x) * F (γ * x) ∂vol =
      ENNReal.ofReal (detNorm E j γ ^ j)⁻¹ *
        ∫⁻ x, ρ x * F x ∂vol := by
    have := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
      (f := fun x : InfinitePlace E → Fin j → Fin j → ℂ => ρ x * F x)
      (g := (mulLin γ).restrictScalars ℝ) (hρm.mul hF) (measurable_mul_left γ)
    rw [hmap, lintegral_smul_measure] at this
    exact this.symm
  calc _ = ∫⁻ x, ENNReal.ofReal (detNorm E j γ ^ j) * (ρ (γ * x) * F (γ * x))
        ∂vol := by
        refine lintegral_congr fun x => ?_
        rw [← mul_assoc, ← h2]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3, ← mul_assoc, ← ENNReal.ofReal_mul hd.le,
          mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one, one_mul]

def emb (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_emb (γ : GL (Fin j) E) (w : InfinitePlace E) :
    Matrix.of (emb γ w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := rfl

/- English proof (translation)
The claim follows from `matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]`.
-/
theorem matInf_mul_assoc (x y z : MatInf E j) : x * y * z = x * (y * z) :=
  matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]

/- English proof (translation)
The claim follows from `matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_mul, map_mul]`.
-/
theorem emb_mul (γ δ : GL (Fin j) E) : emb (γ * δ) = emb γ * emb δ :=
  matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_mul, map_mul]

/- English proof (translation)
The claim follows from `matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_one, map_one, Matrix.one_mul]`.
-/
theorem emb_one_mul (x : MatInf E j) : emb (1 : GL (Fin j) E) * x = x :=
  matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_one, map_one, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[detNorm_pos_iff]`. Introduce `w`. Rewrite using `[of_emb, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)`.
-/
theorem detNorm_emb_pos (γ : GL (Fin j) E) : 0 < detNorm E j (emb γ) := by
  rw [detNorm_pos_iff]
  intro w
  rw [of_emb, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

/- English proof (translation)
Rewrite using `[detNorm_mul]`. Conclude with `mul_pos_iff_of_pos_left (detNorm_emb_pos γ)`.
-/
theorem detNorm_emb_mul_pos (γ : GL (Fin j) E) (x : MatInf E j) :
    0 < detNorm E j (emb γ * x) ↔ 0 < detNorm E j x := by
  rw [detNorm_mul]
  exact mul_pos_iff_of_pos_left (detNorm_emb_pos γ)

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `h1` using `congrArg (fun y : MatInf E j => Matrix.of (y w)) h`. Simplify using `only [of_mul] at h1`. Establish `hu : IsUnit (Matrix.of (x w))` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w))`. Establish `h2` using `hu.mul_right_cancel h1`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Conclude with `w.embedding.injective (congrFun (congrFun h2 a) b)`.
-/
theorem eq_of_emb_mul_eq {γ δ : GL (Fin j) E} {x : MatInf E j} (hx : 0 < detNorm E j x)
    (h : emb γ * x = emb δ * x) : γ = δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 := congrArg (fun y : MatInf E j => Matrix.of (y w)) h
  simp only [of_mul] at h1
  have hu : IsUnit (Matrix.of (x w)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w))
  have h2 := hu.mul_right_cancel h1
  apply Units.ext
  ext a b
  exact w.embedding.injective (congrFun (congrFun h2 a) b)

def autSub (Λ : Submodule (𝓞 E) (Fin j → E)) : Subgroup (GL (Fin j) E) where
  carrier := {γ | ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro γ δ hγ hδ y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hγ, hδ]
  inv_mem' := by
    intro γ hγ y
    rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, h, h'⟩`. Conclude with `⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩`. Introduce and unpack `⟨γ, h, rfl⟩`. Conclude with `⟨γ, h, fun _ _ _ => rfl⟩`.
-/
theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} :
    x ∈ autGL E j Λ ↔ ∃ γ ∈ autSub Λ, x = emb γ := by
  constructor
  · rintro ⟨γ, h, h'⟩
    exact ⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩
  · rintro ⟨γ, h, rfl⟩
    exact ⟨γ, h, fun _ _ _ => rfl⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `hΛ.fg`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) (S ×ˢ (Finset.univ : Finset (Fin j))) (fun p : (Fin j → E) × Fin j => p.1 p.2)`. Establish `h1 : ∀ y ∈ Λ, ∀ a, IsIntegral ℤ (((d : 𝓞 E) : E) * y a)`. Introduce `y hy a`. Rewrite `hy` using `[← hS]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz⟩` from `hd (x, a) (by simpa using hx)`. Establish `: ((d : 𝓞 E) : E) * x a = (z : E)`. Rewrite `hz` using `[Algebra.smul_def]`.

Conclude with `hz.symm`. Rewrite using `[this]`. Conclude with `z.isIntegral_coe`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add x y _ _ hx hy => simpa [mul_add] using hx.add hy`.

Consider the case `smul c x _ hx`. Establish `: ((d : 𝓞 E) : E) * (c • x) a = (c : E) * (((d : 𝓞 E) : E) * x a)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `mul_left_comm _ _ _`. Rewrite using `[this]`.

Conclude with `c.isIntegral_coe.mul hx`. Establish `h2 : ∀ v : Fin j → E, ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Λ`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin j → E))`. Rewrite using `[hΛ.span_eq_top]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩`. Use `choose c hc0 hc using fun b : Fin j => h2 (Pi.single b 1)`.

Use `⟨((d : 𝓞 E) : E) * ((∏ b, c b : 𝓞 E) : E), ?_, ?_⟩` and prove the remaining obligations. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Conclude with `RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)`. Conclude with `RingOfIntegers.coe_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun b _ => hc0 b)`. Introduce `γ hγ a b`.

Establish `h3 : (∏ b, c b) • (Pi.single b 1 : Fin j → E) ∈ Λ`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]`. Conclude with `Λ.smul_mem _ (hc b)`. Establish `h4` using `h1 _ ((hγ _).2 h3) a`. Rewrite `h4` using `[Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, Algebra.smul_def]`.

Rewrite using `[mul_assoc]`. Conclude with `h4`.
-/
theorem exists_denominator (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) :
    ∃ N : E, N ≠ 0 ∧ ∀ γ ∈ autSub Λ, ∀ a b, IsIntegral ℤ (N * (γ : Matrix (Fin j) (Fin j) E) a b) := by
  classical
  obtain ⟨S, hS⟩ := hΛ.fg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (S ×ˢ (Finset.univ : Finset (Fin j))) (fun p : (Fin j → E) × Fin j => p.1 p.2)
  have h1 : ∀ y ∈ Λ, ∀ a, IsIntegral ℤ (((d : 𝓞 E) : E) * y a) := by
    intro y hy a
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz⟩ := hd (x, a) (by simpa using hx)
      have : ((d : 𝓞 E) : E) * x a = (z : E) := by
        rw [Algebra.smul_def] at hz
        exact hz.symm
      rw [this]
      exact z.isIntegral_coe
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
    | smul c x _ hx =>
      have : ((d : 𝓞 E) : E) * (c • x) a = (c : E) * (((d : 𝓞 E) : E) * x a) := by
        rw [Pi.smul_apply, Algebra.smul_def]
        exact mul_left_comm _ _ _
      rw [this]
      exact c.isIntegral_coe.mul hx
  have h2 : ∀ v : Fin j → E, ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin j → E)) := by
      rw [hΛ.span_eq_top]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
  choose c hc0 hc using fun b : Fin j => h2 (Pi.single b 1)
  refine ⟨((d : 𝓞 E) : E) * ((∏ b, c b : 𝓞 E) : E), ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · exact RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)
    · exact RingOfIntegers.coe_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun b _ => hc0 b)
  · intro γ hγ a b
    have h3 : (∏ b, c b) • (Pi.single b 1 : Fin j → E) ∈ Λ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]
      exact Λ.smul_mem _ (hc b)
    have h4 := h1 _ ((hγ _).2 h3) a
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, Algebra.smul_def] at h4
    rw [mul_assoc]
    exact h4

/- English proof (translation)
Take `⟨N, hN, h⟩` from `exists_denominator Λ hΛ`. Use `set B : ℝ := (∑ φ : E →+* ℂ, ‖φ N‖) * C`. Establish `hf` using `NumberField.Embeddings.finite_of_norm_le E ℂ B`. Use `Set.Finite.of_finite_image (f := fun γ : GL (Fin j) E => fun a b => N * (γ : Matrix (Fin j) (Fin j) E) a b) ((Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => hf).subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b`.

Use `⟨h γ hγ a b, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul]`. Establish `h1 : ‖φ ((γ : Matrix (Fin j) (Fin j) E) a b)‖ ≤ C`. Use `hb (InfinitePlace.mk φ) a b` as an intermediate fact. Rewrite `this` using `[emb, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]`. Then use the resulting hypothesis.

Use `mul_le_mul ?_ h1 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ N‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)`. Introduce `γ _ δ _ hγδ`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`.

Conclude with `mul_left_cancel₀ hN (congrFun (congrFun hγδ a) b)`.
-/
theorem finite_bounded (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (C : ℝ) :
    {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ ∀ w a b, ‖emb γ w a b‖ ≤ C}.Finite := by
  obtain ⟨N, hN, h⟩ := exists_denominator Λ hΛ
  set B : ℝ := (∑ φ : E →+* ℂ, ‖φ N‖) * C
  have hf := NumberField.Embeddings.finite_of_norm_le E ℂ B
  refine Set.Finite.of_finite_image (f := fun γ : GL (Fin j) E => fun a b => N * (γ : Matrix (Fin j) (Fin j) E) a b)
    ((Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => hf).subset ?_) ?_
  · rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
    refine ⟨h γ hγ a b, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    have h1 : ‖φ ((γ : Matrix (Fin j) (Fin j) E) a b)‖ ≤ C := by
      have := hb (InfinitePlace.mk φ) a b
      rwa [emb, InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at this
    refine mul_le_mul ?_ h1 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    exact Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ N‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  · intro γ _ δ _ hγδ
    apply Units.ext
    ext a b
    exact mul_left_cancel₀ hN (congrFun (congrFun hγδ a) b)

def nrm (x : MatInf E j) : ℝ := ‖(show InfinitePlace E → Fin j → Fin j → ℂ from x)‖

/- English proof (translation)
The claim follows from `(norm_le_pi_norm (x w a) b).trans ((norm_le_pi_norm (x w) a).trans (norm_le_pi_norm (show InfinitePlace E → Fin j → Fin j → ℂ from x) w))`.
-/
theorem entry_le_nrm (x : MatInf E j) (w a b) : ‖x w a b‖ ≤ nrm x :=
  (norm_le_pi_norm (x w a) b).trans ((norm_le_pi_norm (x w) a).trans
    (norm_le_pi_norm (show InfinitePlace E → Fin j → Fin j → ℂ from x) w))

/- English proof (translation)
Set `y : MatInf E j` to `fun w a b => (Matrix.of (x w))⁻¹ a b`. Use `(finite_bounded Λ hΛ (∑ _c : Fin j, C * nrm y)).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨hγ, hC⟩`. Use `⟨hγ, fun w a b => ?_⟩` and prove the remaining obligations. Establish `h1 : Matrix.of (emb γ w) = Matrix.of ((emb γ * x) w) * Matrix.of (y w)`.

Rewrite using `[of_mul, Matrix.mul_assoc]`. Express the relevant statement in the definitionally equal form `_ = _ * (_ * (Matrix.of (x w))⁻¹)`. Rewrite using `[Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w)), Matrix.mul_one]`. Establish `h2 : emb γ w a b = ∑ c, (emb γ * x) w a c * y w c b` using `congrFun (congrFun h1 a) b`. Rewrite using `[h2]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h3` using `(entry_le_nrm (emb γ * x) w a c).trans hC`. Conclude with `mul_le_mul h3 (entry_le_nrm y w c b) (norm_nonneg _) ((norm_nonneg _).trans h3)`.
-/
theorem finite_orbit (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (x : MatInf E j)
    (hx : 0 < detNorm E j x) (C : ℝ) :
    {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ nrm (emb γ * x) ≤ C}.Finite := by
  let y : MatInf E j := fun w a b => (Matrix.of (x w))⁻¹ a b
  refine (finite_bounded Λ hΛ (∑ _c : Fin j, C * nrm y)).subset ?_
  rintro γ ⟨hγ, hC⟩
  refine ⟨hγ, fun w a b => ?_⟩
  have h1 : Matrix.of (emb γ w) = Matrix.of ((emb γ * x) w) * Matrix.of (y w) := by
    rw [of_mul, Matrix.mul_assoc]
    change _ = _ * (_ * (Matrix.of (x w))⁻¹)
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w)), Matrix.mul_one]
  have h2 : emb γ w a b = ∑ c, (emb γ * x) w a c * y w c b := congrFun (congrFun h1 a) b
  rw [h2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul]
  have h3 := (entry_le_nrm (emb γ * x) w a c).trans hC
  exact mul_le_mul h3 (entry_le_nrm y w c b) (norm_nonneg _) ((norm_nonneg _).trans h3)

def scl (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

/- English proof (translation)
Unfold `nrm`. Express the relevant statement in the definitionally equal form `‖t • (show InfinitePlace E → Fin j → Fin j → ℂ from x)‖ = _`. Rewrite using `[norm_smul, Real.norm_of_nonneg ht.le]`.
-/
theorem nrm_scl (t : ℝ) (ht : 0 < t) (x : MatInf E j) : nrm (scl t x) = t * nrm x := by
  unfold nrm
  change ‖t • (show InfinitePlace E → Fin j → Fin j → ℂ from x)‖ = _
  rw [norm_smul, Real.norm_of_nonneg ht.le]

/- English proof (translation)
Use function extensionality and compare the values at `w a b`. Simplify using `[scl, mul_assoc]`.
-/
theorem scl_scl (s t : ℝ) (x : MatInf E j) : scl s (scl t x) = scl (s * t) x := by
  funext w a b
  simp [scl, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `w a b`. Express the relevant statement in the definitionally equal form `∑ c, y w a c * ((t : ℂ) * x w c b) = (t : ℂ) * ∑ c, y w a c * x w c b`. Simplify using `[Finset.mul_sum, mul_left_comm]`.
-/
theorem mul_scl (t : ℝ) (y x : MatInf E j) : y * scl t x = scl t (y * x) := by
  funext w a b
  change ∑ c, y w a c * ((t : ℂ) * x w c b) = (t : ℂ) * ∑ c, y w a c * x w c b
  simp [Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Rewrite `hx`, the goal using `[detNorm_pos_iff]`. Introduce `w`. Establish `: Matrix.of (scl t x w) = (t : ℂ) • Matrix.of (x w)` using `rfl`. Rewrite using `[this, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht.ne')) (hx w)`.
-/
theorem detNorm_scl_pos {t : ℝ} (ht : 0 < t) {x : MatInf E j} (hx : 0 < detNorm E j x) :
    0 < detNorm E j (scl t x) := by
  rw [detNorm_pos_iff] at hx ⊢
  intro w
  have : Matrix.of (scl t x w) = (t : ℂ) • Matrix.of (x w) := rfl
  rw [this, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht.ne')) (hx w)

/- English proof (translation)
The claim follows from `(measurable_norm : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ‖x‖)`.
-/
theorem measurable_nrm : Measurable (nrm : MatInf E j → ℝ) :=
  (measurable_norm : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ‖x‖)

instance standardBorel : StandardBorelSpace (InfinitePlace E → Fin j → Fin j → ℂ) :=
  haveI : StandardBorelSpace (Fin j → ℂ) := StandardBorelSpace.pi_countable
  haveI : StandardBorelSpace (Fin j → Fin j → ℂ) := StandardBorelSpace.pi_countable
  StandardBorelSpace.pi_countable

def dir (x : MatInf E j) : ℝ :=
  embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ) (scl (nrm x)⁻¹ x)

/- English proof (translation)
Use `(measurable_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).comp ?_` and prove the remaining obligations. Use `measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_` and prove the remaining obligations. Establish `h : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => x w a b` using `by fun_prop`. Conclude with `(Complex.measurable_ofReal.comp measurable_nrm.inv).mul h`.
-/
theorem measurable_dir : Measurable (dir : MatInf E j → ℝ) := by
  refine (measurable_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).comp ?_
  refine measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  have h : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => x w a b := by fun_prop
  exact (Complex.measurable_ofReal.comp measurable_nrm.inv).mul h

/- English proof (translation)
Unfold `dir`. Rewrite using `[nrm_scl t ht, scl_scl, mul_inv, mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]`.
-/
theorem dir_scl (t : ℝ) (ht : 0 < t) (x : MatInf E j) : dir (scl t x) = dir x := by
  unfold dir
  rw [nrm_scl t ht, scl_scl, mul_inv, mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]

/- English proof (translation)
Establish `h1` using `(measurableEmbedding_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).injective h'`. Distinguish the cases in `h0 : nrm x = 0`. Establish `hx : (show InfinitePlace E → Fin j → Fin j → ℂ from x) = 0` using `norm_eq_zero.1 h0`. Establish `hy : (show InfinitePlace E → Fin j → Fin j → ℂ from y) = 0` using `norm_eq_zero.1 (h.symm.trans h0)`. Conclude with `hx.trans hy.symm`.

Rewrite `h1` using `[← h]`. Use function extensionality and compare the values at `w a b`. Conclude with `mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero h0)) (congrFun (congrFun (congrFun h1 w) a) b)`.
-/
theorem eq_of_nrm_dir {x y : MatInf E j} (h : nrm x = nrm y) (h' : dir x = dir y) : x = y := by
  have h1 := (measurableEmbedding_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).injective h'
  by_cases h0 : nrm x = 0
  · have hx : (show InfinitePlace E → Fin j → Fin j → ℂ from x) = 0 := norm_eq_zero.1 h0
    have hy : (show InfinitePlace E → Fin j → Fin j → ℂ from y) = 0 := norm_eq_zero.1 (h.symm.trans h0)
    exact hx.trans hy.symm
  · rw [← h] at h1
    funext w a b
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero h0)) (congrFun (congrFun (congrFun h1 w) a) b)

def key (x : MatInf E j) : ℝ ×ₗ ℝ := toLex (nrm x, dir x)

/- English proof (translation)
The claim follows from `Prod.Lex.toLex_le_toLex`.
-/
theorem key_le {x y : MatInf E j} : key x ≤ key y ↔ nrm x < nrm y ∨ nrm x = nrm y ∧ dir x ≤ dir y :=
  Prod.Lex.toLex_le_toLex

/- English proof (translation)
Use `toLex.injective h` as an intermediate fact. Conclude with `eq_of_nrm_dir (congrArg Prod.fst this) (congrArg Prod.snd this)`.
-/
theorem key_inj {x y : MatInf E j} (h : key x = key y) : x = y := by
  have := toLex.injective h
  exact eq_of_nrm_dir (congrArg Prod.fst this) (congrArg Prod.snd this)

def dom (Λ : Submodule (𝓞 E) (Fin j → E)) : Set (MatInf E j) :=
  {x | 0 < detNorm E j x ∧ ∀ γ : autSub Λ, key x ≤ key (emb (γ : GL (Fin j) E) * x)}

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable`. Use `haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))`. Conclude with `Units.val_injective.countable`.
-/
theorem countable_GL : Countable (GL (Fin j) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  exact Units.val_injective.countable

/- English proof (translation)
The claim follows from `measurableSet_lt measurable_const measurable_detNorm`.
-/
theorem measurableSet_pos : MeasurableSet {g | 0 < detNorm E j g} :=
  measurableSet_lt measurable_const measurable_detNorm

/- English proof (translation)
Use `haveI := countable_GL (E := E) (j := j)`. Establish `: dom Λ = {g | 0 < detNorm E j g} ∩ ⋂ γ : autSub Λ, ({x | nrm x < nrm (emb (γ : GL (Fin j) E) * x)} ∪ ({x | nrm x = nrm (emb (γ : GL (Fin j) E) * x)} ∩ {x | dir x ≤ dir (emb (γ : GL (Fin j) E) * x)}))`. Use extensionality with `x`. Simplify using `[dom, key_le]`. Rewrite using `[this]`.

Use `measurableSet_pos.inter (MeasurableSet.iInter fun γ => ?_)` and prove the remaining obligations. Establish `hm` using `measurable_mul_left (emb (γ : GL (Fin j) E))`. Conclude with `(measurableSet_lt measurable_nrm (measurable_nrm.comp hm)).union ((measurableSet_eq_fun measurable_nrm (measurable_nrm.comp hm)).inter (measurableSet_le measurable_dir (measurable_dir.comp hm)))`.
-/
theorem measurableSet_dom (Λ : Submodule (𝓞 E) (Fin j → E)) : MeasurableSet (dom Λ) := by
  haveI := countable_GL (E := E) (j := j)
  have : dom Λ = {g | 0 < detNorm E j g} ∩ ⋂ γ : autSub Λ, ({x | nrm x < nrm (emb (γ : GL (Fin j) E) * x)} ∪
      ({x | nrm x = nrm (emb (γ : GL (Fin j) E) * x)} ∩ {x | dir x ≤ dir (emb (γ : GL (Fin j) E) * x)})) := by
    ext x
    simp [dom, key_le]
  rw [this]
  refine measurableSet_pos.inter (MeasurableSet.iInter fun γ => ?_)
  have hm := measurable_mul_left (emb (γ : GL (Fin j) E))
  exact (measurableSet_lt measurable_nrm (measurable_nrm.comp hm)).union
    ((measurableSet_eq_fun measurable_nrm (measurable_nrm.comp hm)).inter
      (measurableSet_le measurable_dir (measurable_dir.comp hm)))

/- English proof (translation)
Establish `h1 : (1 : GL (Fin j) E) ∈ {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ nrm (emb γ * x) ≤ nrm x}` using `⟨one_mem _, by rw [emb_one_mul]⟩`. Take `⟨γ, hγ, hmin⟩` from `Set.exists_min_image _ (fun γ => key (emb γ * x)) (finite_orbit Λ hΛ x hx (nrm x)) ⟨1, h1⟩`. Use `⟨γ, hγ.1, (detNorm_emb_mul_pos γ x).2 hx, fun δ => ?_⟩` and prove the remaining obligations. Rewrite using `[← matInf_mul_assoc, ← emb_mul]`. Distinguish the cases in `h : nrm (emb ((δ : GL (Fin j) E) * γ) * x) ≤ nrm x`.

Conclude with `hmin _ ⟨mul_mem δ.2 hγ.1, h⟩`. Conclude with `key_le.2 (Or.inl (hγ.2.trans_lt (not_le.1 h)))`.
-/
theorem exists_mul_mem_dom (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (x : MatInf E j)
    (hx : 0 < detNorm E j x) : ∃ γ ∈ autSub Λ, emb γ * x ∈ dom Λ := by
  have h1 : (1 : GL (Fin j) E) ∈ {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ nrm (emb γ * x) ≤ nrm x} :=
    ⟨one_mem _, by rw [emb_one_mul]⟩
  obtain ⟨γ, hγ, hmin⟩ := Set.exists_min_image _ (fun γ => key (emb γ * x)) (finite_orbit Λ hΛ x hx (nrm x))
    ⟨1, h1⟩
  refine ⟨γ, hγ.1, (detNorm_emb_mul_pos γ x).2 hx, fun δ => ?_⟩
  rw [← matInf_mul_assoc, ← emb_mul]
  by_cases h : nrm (emb ((δ : GL (Fin j) E) * γ) * x) ≤ nrm x
  · exact hmin _ ⟨mul_mem δ.2 hγ.1, h⟩
  · exact key_le.2 (Or.inl (hγ.2.trans_lt (not_le.1 h)))

/- English proof (translation)
Establish `h1` using `h.2 γ⁻¹`. Rewrite `h1` using `[← matInf_mul_assoc, ← emb_mul, Subgroup.coe_inv, inv_mul_cancel, emb_one_mul]`. Establish `h2` using `key_inj (le_antisymm h1 (hx.2 γ))`. Conclude with `Subtype.ext (eq_of_emb_mul_eq hx.1 (h2.trans (emb_one_mul x).symm))`.
-/
theorem eq_one_of_mem_dom {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} {γ : autSub Λ} (hx : x ∈ dom Λ)
    (h : emb (γ : GL (Fin j) E) * x ∈ dom Λ) : γ = 1 := by
  have h1 := h.2 γ⁻¹
  rw [← matInf_mul_assoc, ← emb_mul, Subgroup.coe_inv, inv_mul_cancel, emb_one_mul] at h1
  have h2 := key_inj (le_antisymm h1 (hx.2 γ))
  exact Subtype.ext (eq_of_emb_mul_eq hx.1 (h2.trans (emb_one_mul x).symm))

/- English proof (translation)
Use `⟨detNorm_scl_pos ht hx.1, fun γ => ?_⟩` and prove the remaining obligations. Use `hx.2 γ` as an intermediate fact. Rewrite `this`, the goal using `[key_le]`. Rewrite using `[mul_scl, nrm_scl t ht, nrm_scl t ht, dir_scl t ht, dir_scl t ht]`. Break down `this with h | ⟨h, h'⟩` into its components or cases.

Conclude with `Or.inl (mul_lt_mul_of_pos_left h ht)`. Conclude with `Or.inr ⟨by rw [h], h'⟩`.
-/
theorem scl_mem_dom {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ dom Λ) {t : ℝ} (ht : 0 < t) :
    scl t x ∈ dom Λ := by
  refine ⟨detNorm_scl_pos ht hx.1, fun γ => ?_⟩
  have := hx.2 γ
  rw [key_le] at this ⊢
  rw [mul_scl, nrm_scl t ht, nrm_scl t ht, dir_scl t ht, dir_scl t ht]
  rcases this with h | ⟨h, h'⟩
  · exact Or.inl (mul_lt_mul_of_pos_left h ht)
  · exact Or.inr ⟨by rw [h], h'⟩

@[reducible] def act (Λ : Submodule (𝓞 E) (Fin j → E)) : MulAction (autSub Λ) (MatInf E j) where
  smul γ x := emb (γ : GL (Fin j) E) * x
  one_smul x := emb_one_mul x
  mul_smul γ δ x := by
    change emb ((γ : GL (Fin j) E) * (δ : GL (Fin j) E)) * x = emb (γ : GL (Fin j) E) * (emb (δ : GL (Fin j) E) * x)
    rw [emb_mul, matInf_mul_assoc]

open scoped Pointwise in
/- English proof (translation)
Use `letI := act Λ`. Use `haveI := countable_GL (E := E) (j := j)`. Establish `: MeasurableConstSMul (autSub Λ) (MatInf E j)` using `⟨fun γ => measurable_mul_left _⟩`. Establish `: SMulInvariantMeasure (autSub Λ) (MatInf E j) ν` using `⟨fun γ s hs => by`. Establish `h` using `hν γ γ.2`.

Use `conv_rhs => rw [← h]`. Rewrite using `[Measure.map_apply (measurable_mul_left _) hs]`. Use the proof step `rfl⟩`. Establish `hF : IsFundamentalDomain (autSub Λ) (dom Λ) ν`. Use `IsFundamentalDomain.mk'' (measurableSet_dom Λ).nullMeasurableSet ?_ ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [(h0 : ∀ᵐ g ∂ν, g ∈ {g | 0 < detNorm E j g})] with y hy`. Take `⟨γ, hγ, h⟩` from `exists_mul_mem_dom Λ hΛ y hy`. Conclude with `⟨⟨γ, hγ⟩, h⟩`. Introduce `γ hγ`. Use `Disjoint.aedisjoint (Set.disjoint_left.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩ h`. Conclude with `hγ (eq_one_of_mem_dom hx h)`. Introduce `γ`. Conclude with `(measurePreserving_smul γ ν).quasiMeasurePreserving`. Apply `le_antisymm` to reduce the goal to its premises.

Unfold `covol`. Use `iInf_le_of_le (A ∩ dom Λ) (iInf_le_of_le (hA.inter (measurableSet_dom Λ)) (iInf_le_of_le ?_ le_rfl))` and prove the remaining obligations. Introduce `x hx`. Take `⟨γ, hγ, h⟩` from `exists_mul_mem_dom Λ hΛ x (hAX hx)`. Establish `hγ' : emb γ ∈ autGL E j Λ` using `mem_autGL.2 ⟨γ, hγ, rfl⟩`.

Conclude with `⟨emb γ, hγ', hinv _ hγ' x hx, h⟩`. Unfold `covol`. Use `le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_` and prove the remaining obligations. Rewrite using `[hF.measure_eq_tsum D]`. Use `le_trans (measure_mono ?_) (measure_iUnion_le _)` and prove the remaining obligations.

Introduce and unpack `x ⟨hx, hxf⟩`. Take `⟨_, hγ', h⟩` from `hD x hx`. Take `⟨γ, hγ, rfl⟩` from `mem_autGL.1 hγ'`. Use `Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : autSub Λ)⁻¹, ?_, hxf⟩` and prove the remaining obligations. Rewrite using `[Set.mem_inv_smul_set_iff]`.

Conclude with `h`.
-/
theorem covol_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (ν : Measure (MatInf E j))
    (hν : ∀ γ ∈ autSub Λ, ν.map (fun x => emb γ * x) = ν) (h0 : ν {g | 0 < detNorm E j g}ᶜ = 0)
    (A : Set (MatInf E j)) (hA : MeasurableSet A) (hAX : A ⊆ {g | 0 < detNorm E j g})
    (hinv : ∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) : covol (autGL E j Λ) ν A = ν (A ∩ dom Λ) := by
  letI := act Λ
  haveI := countable_GL (E := E) (j := j)
  have : MeasurableConstSMul (autSub Λ) (MatInf E j) := ⟨fun γ => measurable_mul_left _⟩
  have : SMulInvariantMeasure (autSub Λ) (MatInf E j) ν := ⟨fun γ s hs => by
    have h := hν γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_mul_left _) hs]
    rfl⟩
  have hF : IsFundamentalDomain (autSub Λ) (dom Λ) ν := by
    refine IsFundamentalDomain.mk'' (measurableSet_dom Λ).nullMeasurableSet ?_ ?_ ?_
    · filter_upwards [(h0 : ∀ᵐ g ∂ν, g ∈ {g | 0 < detNorm E j g})] with y hy
      obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ y hy
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
      rintro _ ⟨x, hx, rfl⟩ h
      exact hγ (eq_one_of_mem_dom hx h)
    · intro γ
      exact (measurePreserving_smul γ ν).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ dom Λ) (iInf_le_of_le (hA.inter (measurableSet_dom Λ)) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ x (hAX hx)
    have hγ' : emb γ ∈ autGL E j Λ := mem_autGL.2 ⟨γ, hγ, rfl⟩
    exact ⟨emb γ, hγ', hinv _ hγ' x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨_, hγ', h⟩ := hD x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_autGL.1 hγ'
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : autSub Λ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

/- English proof (translation)
Introduce `E _ _ _ j Λ hΛ`. Use `⟨dom Λ, measurableSet_dom Λ, fun x hx => hx.1, ?_, fun g hg t ht => scl_mem_dom hg ht, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨γ, hγ, h⟩` from `exists_mul_mem_dom Λ hΛ g hg`. Conclude with `⟨emb γ, mem_autGL.2 ⟨γ, hγ, rfl⟩, h⟩`.

Introduce `G A hG hGinv hA hAX hinv`. Establish `hAD` using `hA.inter (measurableSet_dom Λ)`. Rewrite using `[covol_eq Λ hΛ _ ?_ ?_ A hA hAX hinv]`. Rewrite using `[withDensity_apply _ hAD, Measure.restrict_restrict hAD, Set.inter_eq_left.2 (Set.inter_subset_left.trans hAX)]`. Introduce `γ hγ`.

Rewrite using `[← withDensity_indicator measurableSet_pos]`. Use `set G' : MatInf E j → ENNReal := {g | 0 < detNorm E j g}.indicator G with hG'`. Establish `hG1 : Measurable G'` using `hG`. Establish `hG2 : ∀ x, G' (emb γ * x) = G' x`. Introduce `x`.

Distinguish the cases in `hx : 0 < detNorm E j x`. Rewrite using `[hG', Set.indicator_of_mem (show x ∈ {g | 0 < detNorm E j g} from hx), Set.indicator_of_mem (show emb γ * x ∈ {g | 0 < detNorm E j g} from (detNorm_emb_mul_pos γ x).2 hx)]`. Conclude with `hGinv _ (mem_autGL.2 ⟨γ, hγ, rfl⟩) x hx`. Rewrite using `[hG', Set.indicator_of_notMem (show x ∉ {g | 0 < detNorm E j g} from hx), Set.indicator_of_notMem (show emb γ * x ∉ {g | 0 < detNorm E j g} from fun h => hx ((detNorm_emb_mul_pos γ x).1 h))]`. Use extensionality with `s hs`.

Establish `hm` using `measurable_mul_left (emb γ)`. Rewrite using `[Measure.map_apply hm hs, withDensity_apply _ hs, withDensity_apply _ (hm hs), ← lintegral_indicator hs, ← lintegral_indicator (hm hs), ← lintegral_haarGL_mul_left (emb γ) (detNorm_emb_pos γ) _ (hG1.indicator hs)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : emb γ * x ∈ s`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => emb γ * x) ⁻¹' s from hx), hG2]`.

Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => emb γ * x) ⁻¹' s from hx)]`. Use `withDensity_absolutelyContinuous _ _ ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply measurableSet_pos.compl, Set.compl_inter_self, measure_empty]`.
-/
theorem exists_cone_domain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  intro E _ _ _ j Λ hΛ
  refine ⟨dom Λ, measurableSet_dom Λ, fun x hx => hx.1, ?_, fun g hg t ht => scl_mem_dom hg ht, ?_⟩
  · intro g hg
    obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ g hg
    exact ⟨emb γ, mem_autGL.2 ⟨γ, hγ, rfl⟩, h⟩
  intro G A hG hGinv hA hAX hinv
  have hAD := hA.inter (measurableSet_dom Λ)
  rw [covol_eq Λ hΛ _ ?_ ?_ A hA hAX hinv]
  · rw [withDensity_apply _ hAD, Measure.restrict_restrict hAD,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hAX)]
  · intro γ hγ
    rw [← withDensity_indicator measurableSet_pos]
    set G' : MatInf E j → ENNReal := {g | 0 < detNorm E j g}.indicator G with hG'
    have hG1 : Measurable G' := hG
    have hG2 : ∀ x, G' (emb γ * x) = G' x := by
      intro x
      by_cases hx : 0 < detNorm E j x
      · rw [hG', Set.indicator_of_mem (show x ∈ {g | 0 < detNorm E j g} from hx),
          Set.indicator_of_mem (show emb γ * x ∈ {g | 0 < detNorm E j g} from (detNorm_emb_mul_pos γ x).2 hx)]
        exact hGinv _ (mem_autGL.2 ⟨γ, hγ, rfl⟩) x hx
      · rw [hG', Set.indicator_of_notMem (show x ∉ {g | 0 < detNorm E j g} from hx),
          Set.indicator_of_notMem
            (show emb γ * x ∉ {g | 0 < detNorm E j g} from fun h => hx ((detNorm_emb_mul_pos γ x).1 h))]
    ext s hs
    have hm := measurable_mul_left (emb γ)
    rw [Measure.map_apply hm hs, withDensity_apply _ hs, withDensity_apply _ (hm hs), ← lintegral_indicator hs,
      ← lintegral_indicator (hm hs), ← lintegral_haarGL_mul_left (emb γ) (detNorm_emb_pos γ) _ (hG1.indicator hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : emb γ * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => emb γ * x) ⁻¹' s from hx), hG2]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => emb γ * x) ⁻¹' s from hx)]
  · refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply measurableSet_pos.compl, Set.compl_inter_self, measure_empty]

end GlobalTheory.LatDom
