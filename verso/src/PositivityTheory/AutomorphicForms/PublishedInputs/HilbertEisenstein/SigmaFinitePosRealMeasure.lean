import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Simplify using `only [absD, map_mul, Positive.val_mul]`.
-/
theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  simp only [absD, map_mul, Positive.val_mul]

/- English proof (translation)
The claim follows from `(IdeleGroup.ideleModule F _).2`.
-/
theorem absD_pos (g : GA F 2) : 0 < absD g := (IdeleGroup.ideleModule F _).2

/- English proof (translation)
Rewrite using `[ideleModule_apply]`. Establish `h2 : finiteModule (UpperTheory.V.TR.infId F d) = 1`. Use `finprod_eq_one_of_forall_eq_one fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).2 v‖ = 1`. Express the relevant statement in the definitionally equal form `‖((1 : Af F) - 0 + 0) v‖ = 1`.

Simplify using the standard rewrite rules. Rewrite using `[h2, mul_one, infiniteModule]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hm : w.mult = 1`. Unfold `InfinitePlace.mult`.

Rewrite using `[if_pos (IsTotallyReal.isReal w)]`. Rewrite using `[hm, pow_one]`. Express the relevant statement in the definitionally equal form `‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).1 w‖ = _`. Express the relevant statement in the definitionally equal form `‖((1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F (d : UpperTheory.V.TR.Rinf F)) w‖ = _`. Rewrite using `[map_one, sub_self, zero_add]`.

Express the relevant statement in the definitionally equal form `‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((d : UpperTheory.V.TR.Rinf F) w)‖ = _`. Use `set e := InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)`. Establish `he : ∀ r, (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r = e.symm r` using `fun _ => rfl`. Rewrite using `[he, ← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right]`. Establish `h0 : e.symm 0 = 0`.

Rewrite using `[← he]`. Conclude with `map_zero _`. Rewrite using `[← h0, e.symm.dist_eq]`.
-/
theorem ideleModule_infId (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F d) : ℝ) = ∏ v, |(d : UpperTheory.V.TR.Rinf F) v| := by
  rw [ideleModule_apply]
  have h2 : finiteModule (UpperTheory.V.TR.infId F d) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).2 v‖ = 1
    change ‖((1 : Af F) - 0 + 0) v‖ = 1
    simp
  rw [h2, mul_one, infiniteModule]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 1 := by
    unfold InfinitePlace.mult; rw [if_pos (IsTotallyReal.isReal w)]
  rw [hm, pow_one]
  change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).1 w‖ = _
  change ‖((1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F (d : UpperTheory.V.TR.Rinf F)) w‖ = _
  rw [map_one, sub_self, zero_add]
  change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((d : UpperTheory.V.TR.Rinf F) w)‖ = _
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ r, (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r = e.symm r :=
    fun _ => rfl
  rw [he, ← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right]
  have h0 : e.symm 0 = 0 := by
    rw [← he]; exact map_zero _
  rw [← h0, e.symm.dist_eq]

/- English proof (translation)
Rewrite using `[absD, UpperTheory.V.TR.det_infGL, ideleModule_infId]`. Both sides reduce to the same expression.
-/
theorem absD_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    absD (UpperTheory.V.TR.infGL F 2 y) = ∏ v, |(Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v| := by
  rw [absD, UpperTheory.V.TR.det_infGL, ideleModule_infId]
  rfl

/- English proof (translation)
Rewrite using `[absD_mul]`. Use `congr 1`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F))) = (moduleSection (w0 F) t * (u : Ideles F)) ^ 2`. Use `ext`. Simplify using `[sq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu : IdeleGroup.ideleModule F (u : Ideles F) = 1` using `u.2`. Rewrite using `[absD, hdet, map_pow, map_mul, ideleModule_moduleSection, hu, mul_one]`. Both sides reduce to the same expression.
-/
theorem absD_scalar_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g) =
      (t : ℝ) ^ 2 * absD g := by
  rw [absD_mul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F))) = (moduleSection (w0 F) t * (u : Ideles F)) ^ 2 := by
    ext
    simp [sq]
    ring
  have hu : IdeleGroup.ideleModule F (u : Ideles F) = 1 := u.2
  rw [absD, hdet, map_pow, map_mul, ideleModule_moduleSection, hu, mul_one]
  rfl

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `hχ.exists_pow_eq_one`. Establish `h1 : (χ.1 a) ^ n = 1`. Use `congrArg (fun ψ : HChar F => ψ.1 a) hpow` as an intermediate fact. Simplify using `using this`. Establish `h2 : ‖((χ.1 a : ℂˣ) : ℂ)‖ ^ n = 1`.

Rewrite using `[← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2`.
-/
theorem norm_hchar_of_finOrder {χ : HChar F} (hχ : IsOfFinOrder χ) (a : Ideles F) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  have h1 : (χ.1 a) ^ n = 1 := by
    have := congrArg (fun ψ : HChar F => ψ.1 a) hpow
    simpa using this
  have h2 : ‖((χ.1 a : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

/- English proof (translation)
The claim follows from `expPosHomeomorph.measurableEmbedding`.
-/
theorem measurableEmbedding_expPos : MeasurableEmbedding expPos :=
  expPosHomeomorph.measurableEmbedding

instance sigmaFinite_posRealMeasure : SigmaFinite posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  exact measurableEmbedding_expPos.sigmaFinite_map

/- English proof (translation)
The claim follows from `measurable_subtype_coe measurableSet_Ici`.
-/
theorem measurableSet_ge_one : MeasurableSet {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} :=
  measurable_subtype_coe measurableSet_Ici

/- English proof (translation)
The claim follows from `measurable_subtype_coe measurableSet_Iio`.
-/
theorem measurableSet_lt_one : MeasurableSet {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} :=
  measurable_subtype_coe measurableSet_Iio

/- English proof (translation)
Rewrite using `[posRealMeasure_eq_map_expPos, IntegrableOn, measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]`. Establish `hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} = Set.Ici 0`. Use extensionality with `x`. Simplify using `[Real.one_le_exp_iff]`. Rewrite using `[hpre]`.

Establish `hf : (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) ∘ expPos = fun x => Real.exp ((1 - (r : ℝ)) * x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, coe_expPos]`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Establish `hneg : (1 - (r : ℝ)) < 0`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `(integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm`.
-/
theorem integrableOn_ge_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) {t | 1 ≤ (t : ℝ)} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} = Set.Ici 0 := by
    ext x; simp [Real.one_le_exp_iff]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) ∘ expPos =
      fun x => Real.exp ((1 - (r : ℝ)) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hneg : (1 - (r : ℝ)) < 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm

/- English proof (translation)
Rewrite using `[posRealMeasure_eq_map_expPos, IntegrableOn, measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]`. Establish `hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} = Set.Iio 0`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, coe_expPos, Set.mem_Iio]`. Rewrite using `[← Real.exp_zero, Real.exp_lt_exp]`.

Rewrite using `[hpre]`. Establish `hf : (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) ∘ expPos = fun x => Real.exp (((r : ℝ) - 1) * x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, coe_expPos]`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Establish `hpos : 0 < ((r : ℝ) - 1)`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(integrableOn_exp_mul_Iic hpos 0).mono_set Set.Iio_subset_Iic_self`.
-/
theorem integrableOn_lt_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) {t | (t : ℝ) < 1} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, coe_expPos, Set.mem_Iio]
    rw [← Real.exp_zero, Real.exp_lt_exp]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) ∘ expPos =
      fun x => Real.exp (((r : ℝ) - 1) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hpos : 0 < ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Iic hpos 0).mono_set Set.Iio_subset_Iic_self

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
