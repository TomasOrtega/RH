import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom : Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E))` using `continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap`. Conclude with `Continuous.units_map _ hM`.
-/
private theorem cont_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp continuous_adelicChar`.
-/
private theorem cont_ψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
private theorem norm_ψ (x : A ℚ) : ‖ψ x‖ = 1 := Circle.norm_coe _

/- English proof (translation)
The claim follows from `UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))`.
-/
private theorem cont_nE (D : Dat ℚ E) : Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [Measure.restrict_apply_univ] have h : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 := GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain rw [h] exact ENNReal.one_lt_top⟩`.
-/
private theorem finite_fundamentalSet_measure : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    have h : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 := GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
    rw [h]
    exact ENNReal.one_lt_top⟩

/- English proof (translation)
Use `haveI := finite_fundamentalSet_measure`. Use `continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_` and prove the remaining obligations. Conclude with `fun x => ((hc.comp ((cont_nE D).mul continuous_const)).mul (cont_ψ.comp (continuous_apply 1))).aestronglyMeasurable`. Conclude with `fun x => ae_of_all _ fun u => by rw [norm_mul, norm_ψ, mul_one]; exact hB _`. Conclude with `ae_of_all _ fun u => (hc.comp (continuous_const.mul hh)).mul continuous_const`.
-/
private theorem cont_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ}
    (hB : ∀ g, ‖φ g‖ ≤ B) {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {h : X → GL (Fin 2) (A E)} (hh : Continuous h) : Continuous fun x => Wo D φ (h x) := by
  haveI := finite_fundamentalSet_measure
  refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact fun x => ((hc.comp ((cont_nE D).mul continuous_const)).mul
      (cont_ψ.comp (continuous_apply 1))).aestronglyMeasurable
  · exact fun x => ae_of_all _ fun u => by rw [norm_mul, norm_ψ, mul_one]; exact hB _
  · exact ae_of_all _ fun u => (hc.comp (continuous_const.mul hh)).mul continuous_const

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map ((TR.continuous_infEq ℚ).prodMk continuous_const : Continuous fun x : TR.Rinf ℚ => ((TR.infEq ℚ x, 0) : InfiniteAdeleRing ℚ × Af ℚ))))`.
-/
private theorem cont_infGL : Continuous (TR.infGL ℚ 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq ℚ).prodMk continuous_const :
    Continuous fun x : TR.Rinf ℚ => ((TR.infEq ℚ x, 0) : InfiniteAdeleRing ℚ × Af ℚ))))

/- English proof (translation)
Use `cont_infGL.comp (Matrix.SpecialLinearGroup.continuous_toGL.comp ?_)` and prove the remaining obligations. Use `continuous_induced_rng.2 (continuous_matrix fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> refine continuous_pi fun _ => ?_ <;> fun_prop`.
-/
private theorem cont_rot : Continuous rot := by
  refine cont_infGL.comp (Matrix.SpecialLinearGroup.continuous_toGL.comp ?_)
  refine continuous_induced_rng.2 (continuous_matrix fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> refine continuous_pi fun _ => ?_ <;> fun_prop

private def uu (y : ({0}ᶜ : Set ℝ)) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y.1, fun _ => y.1⁻¹, funext fun _ => mul_inv_cancel₀ y.2, funext fun _ => inv_mul_cancel₀ y.2⟩

/- English proof (translation)
The claim follows from `dif_neg y.2`.
-/
private theorem iy_uu (y : ({0}ᶜ : Set ℝ)) : iy y.1 = TR.infId ℚ (uu y) := dif_neg y.2

/- English proof (translation)
Simplify using `only [iy_uu]`. Use `(TR.continuous_infId ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `continuous_pi fun _ => continuous_subtype_val`. Conclude with `continuous_pi fun _ => continuous_subtype_val.inv₀ fun y => y.2`.
-/
private theorem cont_iy : Continuous fun y : ({0}ᶜ : Set ℝ) => iy y.1 := by
  simp only [iy_uu]
  refine (TR.continuous_infId ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact continuous_pi fun _ => continuous_subtype_val
  · exact continuous_pi fun _ => continuous_subtype_val.inv₀ fun y => y.2

/- English proof (translation)
Establish `h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x` using `fun x => (TR.infEq ℚ).symm_apply_apply x`. Express the relevant statement in the definitionally equal form `TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _`. Simplify using `[h]`.
-/
private theorem pInf_inf (x : (TR.Rinf ℚ)ˣ) : TR.pInf ℚ (TR.infId ℚ x).val = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _
  simp [h]

/- English proof (translation)
Use `iy_uu ⟨y, hy⟩` as an intermediate fact. Simplify using `only at this`. Rewrite using `[re, this, pInf_inf]`. Both sides reduce to the same expression.
-/
private theorem re_iy {y : ℝ} (hy : y ≠ 0) : re (iy y : A ℚ) = y := by
  have := iy_uu ⟨y, hy⟩
  simp only at this
  rw [re, this, pInf_inf]
  rfl

/- English proof (translation)
Establish `hC : IsCompact ((fun t => em E (rot t)) '' Set.Icc (0 : ℝ) (2 * Real.pi))` using `isCompact_Icc.image (cont_em.comp cont_rot)`. Take `⟨K, -, hK⟩` from `hφ.wdec _ hC`. Take `⟨B, hB⟩` from `hK r`. Use `⟨|B|, abs_nonneg _, fun t ht y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hB (iy y) (em E (rot t)) ⟨t, ht, rfl⟩).1`.

Rewrite `h1` using `[re_iy hy, ← map_mul]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))`.
-/
private theorem w_bd (D : Dat ℚ E) {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (hφ : admitted D ω φ) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ y : ℝ, y ≠ 0 →
      ‖Wo D φ (em E (aE (iy y) * rot t))‖ ≤ B * ((1 + |y|) ^ r)⁻¹ := by
  have hC : IsCompact ((fun t => em E (rot t)) '' Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.image (cont_em.comp cont_rot)
  obtain ⟨K, -, hK⟩ := hφ.wdec _ hC
  obtain ⟨B, hB⟩ := hK r
  refine ⟨|B|, abs_nonneg _, fun t ht y hy => ?_⟩
  have h1 := (hB (iy y) (em E (rot t)) ⟨t, ht, rfl⟩).1
  rw [re_iy hy, ← map_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

private def G (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (t y : ℝ) : ℂ :=
  Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)

/- English proof (translation)
The claim follows from `compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))`.
-/
private theorem ae_ne : ∀ᵐ y : ℝ, y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))

/- English proof (translation)
Use `set m := ⌈s.re⌉₊ with hm`. Take `⟨B, hB0, hB⟩` from `w_bd D hφ (k + m + 2)`. Use `⟨B, hB0, fun t ht y hy => ?_⟩` and prove the remaining obligations. Establish `hy0 : 0 < |y|` using `abs_pos.2 hy`. Use `set a := 1 + |y| with ha`.

Establish `ha1 : 1 ≤ a` using `by rw [ha]; linarith`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hya : |y| ≤ a` using `by rw [ha]; linarith`. Establish `hσ : 0 ≤ s.re - 2` using `by linarith`. Establish `hm' : s.re - 2 ≤ (m : ℝ)`.

Use `Nat.le_ceil s.re` as an intermediate fact. Rewrite `this` using `[← hm]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : |y| ^ (s.re - 2) ≤ a ^ m`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ‖G D χ k φ s t y‖ = ‖Wo D φ (em E (aE (iy y) * rot t))‖ * |y| ^ k * |y| ^ (s.re - 2)`. Simplify using `only [G, norm_mul, hχ, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos hy0]`. Simplify using the standard rewrite rules. Establish `e3 : 1 + y ^ 2 ≤ a ^ 2`.

Rewrite using `[ha]`. Use polynomial arithmetic with `[abs_nonneg y, sq_abs y]`. Rewrite using `[e2]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hB t ht y hy`.

Use `_ = B * (a ^ 2)⁻¹ := by`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ B * (1 + y ^ 2)⁻¹ := by gcongr`.
-/
private theorem G_bd (D : Dat ℚ E) {ω χ : HChar ℚ} (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hφ : admitted D ω φ) (k : ℕ) {s : ℂ} (hs : 4 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∀ y : ℝ, y ≠ 0 →
      ‖G D χ k φ s t y‖ ≤ B * (1 + y ^ 2)⁻¹ := by
  set m := ⌈s.re⌉₊ with hm
  obtain ⟨B, hB0, hB⟩ := w_bd D hφ (k + m + 2)
  refine ⟨B, hB0, fun t ht y hy => ?_⟩
  have hy0 : 0 < |y| := abs_pos.2 hy
  set a := 1 + |y| with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  have hya : |y| ≤ a := by rw [ha]; linarith
  have hσ : 0 ≤ s.re - 2 := by linarith
  have hm' : s.re - 2 ≤ (m : ℝ) := by
    have := Nat.le_ceil s.re
    rw [← hm] at this
    linarith
  have e1 : |y| ^ (s.re - 2) ≤ a ^ m := by
    calc |y| ^ (s.re - 2) ≤ a ^ (s.re - 2) := Real.rpow_le_rpow hy0.le hya hσ
      _ ≤ a ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hm'
      _ = a ^ m := Real.rpow_natCast a m
  have e2 : ‖G D χ k φ s t y‖ = ‖Wo D φ (em E (aE (iy y) * rot t))‖ * |y| ^ k * |y| ^ (s.re - 2) := by
    simp only [G, norm_mul, hχ, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    simp
  have e3 : 1 + y ^ 2 ≤ a ^ 2 := by
    rw [ha]
    nlinarith [abs_nonneg y, sq_abs y]
  rw [e2]
  calc ‖Wo D φ (em E (aE (iy y) * rot t))‖ * |y| ^ k * |y| ^ (s.re - 2)
      ≤ (B * (a ^ (k + m + 2))⁻¹) * a ^ k * a ^ m := by
        gcongr
        exact hB t ht y hy
    _ = B * (a ^ 2)⁻¹ := by
        field_simp
        ring
    _ ≤ B * (1 + y ^ 2)⁻¹ := by
        gcongr

/- English proof (translation)
Establish `hcont : ContinuousOn (G D χ k φ s t) ({0}ᶜ : Set ℝ)`. Use `continuousOn_iff_continuous_restrict.2 ?_` and prove the remaining obligations. Establish `h1 : Continuous fun y : ({0}ᶜ : Set ℝ) => Wo D φ (em E (aE (iy y.1) * rot t))` using `cont_Wo D hc hB (cont_em.comp ((continuous_aE.comp cont_iy).mul continuous_const))`. Establish `h2 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((χ.1 (iy y.1) : ℂˣ) : ℂ)` using `Units.continuous_val.comp (χ.2.1.comp cont_iy)`. Establish `h3 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((y.1 : ℝ) : ℂ) ^ k` using `(Complex.continuous_ofReal.comp continuous_subtype_val).pow k`.

Establish `h4 : Continuous fun y : ({0}ᶜ : Set ℝ) => (((|y.1| : ℝ)) : ℂ) ^ (s - 2)` using `Continuous.cpow (Complex.continuous_ofReal.comp (continuous_abs.comp continuous_subtype_val)) continuous_const fun y => Complex.ofReal_mem_slitPlane.2 (abs_pos.2 y.2)`. Conclude with `((h1.mul h2).mul h3).mul h4`. Establish `h` using `hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl`. Rewrite `h` using `[Measure.restrict_eq_self_of_ae_mem (s := ({0}ᶜ : Set ℝ)) ae_ne]`. Then use the resulting hypothesis.
-/
private theorem G_meas (D : Dat ℚ E) (χ : HChar ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ}
    (hB : ∀ g, ‖φ g‖ ≤ B) (k : ℕ) (s : ℂ) (t : ℝ) : AEStronglyMeasurable (G D χ k φ s t) volume := by
  have hcont : ContinuousOn (G D χ k φ s t) ({0}ᶜ : Set ℝ) := by
    refine continuousOn_iff_continuous_restrict.2 ?_
    have h1 : Continuous fun y : ({0}ᶜ : Set ℝ) => Wo D φ (em E (aE (iy y.1) * rot t)) :=
      cont_Wo D hc hB (cont_em.comp ((continuous_aE.comp cont_iy).mul continuous_const))
    have h2 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((χ.1 (iy y.1) : ℂˣ) : ℂ) :=
      Units.continuous_val.comp (χ.2.1.comp cont_iy)
    have h3 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((y.1 : ℝ) : ℂ) ^ k :=
      (Complex.continuous_ofReal.comp continuous_subtype_val).pow k
    have h4 : Continuous fun y : ({0}ᶜ : Set ℝ) => (((|y.1| : ℝ)) : ℂ) ^ (s - 2) :=
      Continuous.cpow (Complex.continuous_ofReal.comp (continuous_abs.comp continuous_subtype_val))
        continuous_const fun y => Complex.ofReal_mem_slitPlane.2 (abs_pos.2 y.2)
    exact ((h1.mul h2).mul h3).mul h4
  have h := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem (s := ({0}ᶜ : Set ℝ)) ae_ne] at h

/- English proof (translation)
Take `⟨B, -, hB⟩` from `G_bd D hχ hφ k hs`. Take `⟨C, hC⟩` from `hφ.bdd`. Use `Integrable.mono' (integrable_inv_one_add_sq.const_mul B) (G_meas D χ hφ.cont hC k s t) ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne] with y hy using hB t ht y hy`.
-/
private theorem G_int (D : Dat ℚ E) {ω χ : HChar ℚ} (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hφ : admitted D ω φ) (k : ℕ) {s : ℂ} (hs : 4 < s.re) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) : Integrable (G D χ k φ s t) := by
  obtain ⟨B, -, hB⟩ := G_bd D hχ hφ k hs
  obtain ⟨C, hC⟩ := hφ.bdd
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul B) (G_meas D χ hφ.cont hC k s t) ?_
  filter_upwards [ae_ne] with y hy using hB t ht y hy

/- English proof (translation)
Take `⟨B, -, hB⟩` from `G_bd D hχ hφ k hs`. Take `⟨C, hC⟩` from `hφ.bdd`. Use `continuousOn_of_dominated (bound := fun y => B * (1 + y ^ 2)⁻¹) (fun t _ => G_meas D χ hφ.cont hC k s t) (fun t ht => ?_) (integrable_inv_one_add_sq.const_mul B) ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne] with y hy using hB t ht y hy`. Use `ae_of_all _ fun y => Continuous.continuousOn ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun t => Wo D φ (em E (aE (iy y) * rot t))` using `cont_Wo D hφ.cont hC (cont_em.comp (continuous_const.mul cont_rot))`. Conclude with `((h1.mul continuous_const).mul continuous_const).mul continuous_const`.
-/
private theorem I_cont (D : Dat ℚ E) {ω χ : HChar ℚ} (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hφ : admitted D ω φ) (k : ℕ) {s : ℂ} (hs : 4 < s.re) :
    ContinuousOn (fun t => ∫ y, G D χ k φ s t y) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  obtain ⟨B, -, hB⟩ := G_bd D hχ hφ k hs
  obtain ⟨C, hC⟩ := hφ.bdd
  refine continuousOn_of_dominated (bound := fun y => B * (1 + y ^ 2)⁻¹)
    (fun t _ => G_meas D χ hφ.cont hC k s t) (fun t ht => ?_) (integrable_inv_one_add_sq.const_mul B) ?_
  · filter_upwards [ae_ne] with y hy using hB t ht y hy
  · refine ae_of_all _ fun y => Continuous.continuousOn ?_
    have h1 : Continuous fun t => Wo D φ (em E (aE (iy y) * rot t)) :=
      cont_Wo D hφ.cont hC (cont_em.comp (continuous_const.mul cont_rot))
    exact ((h1.mul continuous_const).mul continuous_const).mul continuous_const

/- English proof (translation)
Use `(MvPolynomial.continuous_eval q).comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Use `fin_cases i`. Conclude with `Complex.continuous_ofReal.comp Real.continuous_sin`. Conclude with `Complex.continuous_ofReal.comp Real.continuous_cos`.
-/
private theorem cont_ev (q : MvPolynomial (Fin 2) ℂ) :
    Continuous fun t : ℝ => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] q := by
  refine (MvPolynomial.continuous_eval q).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact Complex.continuous_ofReal.comp Real.continuous_sin
  · exact Complex.continuous_ofReal.comp Real.continuous_cos

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem Mk_eq (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (φ : GL (Fin 2) (A E) → ℂ)
    (p : MvPolynomial (Fin 2) ℂ) (s : ℂ) :
    Mk D χ k φ p s = ∫ t in (0 : ℝ)..2 * Real.pi, MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p *
      ∫ y, G D χ k φ s t y := rfl

/- English proof (translation)
Use `ContinuousOn.intervalIntegrable ?_` and prove the remaining obligations. Rewrite using `[Set.uIcc_of_le (by positivity)]`. Conclude with `(cont_ev q).continuousOn.mul (I_cont D hχ hφ k hs)`.
-/
private theorem ii (D : Dat ℚ E) {ω χ : HChar ℚ} (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hφ : admitted D ω φ) (k : ℕ) {s : ℂ} (hs : 4 < s.re)
    (q : MvPolynomial (Fin 2) ℂ) :
    IntervalIntegrable (fun t => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] q *
      ∫ y, G D χ k φ s t y) volume 0 (2 * Real.pi) := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le (by positivity)]
  exact (cont_ev q).continuousOn.mul (I_cont D hχ hφ k hs)

/- English proof (translation)
Simplify using `only [Mk_eq]`. Rewrite using `[← intervalIntegral.integral_add (ii D hχ a₁ k hs _) (ii D hχ a₂ k hs _), ← intervalIntegral.integral_add (ii D hχ a₀ k hs _) ((ii D hχ a₁ k hs _).add (ii D hχ a₂ k hs _))]`. Use `intervalIntegral.integral_congr fun t ht => ?_` and prove the remaining obligations. Rewrite `ht` using `[Set.uIcc_of_le (by positivity)]`. Establish `hI : ∫ y, G D χ (k + 1) φ s t y = (Real.sin t : ℂ) ^ 2 * (∫ y, G D χ k φ₀ s t y) + ((Real.sin t : ℂ) * (Real.cos t : ℂ) * (∫ y, G D χ k φ₁ s t y) + (Real.cos t : ℂ) ^ 2 * ∫ y, G D χ k φ₂ s t y)`.

Establish `i₀` using `(G_int D hχ a₀ k hs ht).const_mul ((Real.sin t : ℂ) ^ 2)`. Establish `i₁` using `(G_int D hχ a₁ k hs ht).const_mul ((Real.sin t : ℂ) * (Real.cos t : ℂ))`. Establish `i₂` using `(G_int D hχ a₂ k hs ht).const_mul ((Real.cos t : ℂ) ^ 2)`. Establish `i₃ : Integrable (fun x => (Real.sin t : ℂ) * (Real.cos t : ℂ) * G D χ k φ₁ s t x + (Real.cos t : ℂ) ^ 2 * G D χ k φ₂ s t x)` using `i₁.add i₂`. Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂, ← integral_add i₀ i₃]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne] with y hy`. Simplify using `only [G, pow_succ, Pi.add_apply]`. Take the linear combination `(((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) * h y t hy`. Simplify using `only [hI, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem step (D : Dat ℚ E) {ω χ : HChar ℚ} (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ₀ φ₁ φ₂ φ : GL (Fin 2) (A E) → ℂ} (a₀ : admitted D ω φ₀) (a₁ : admitted D ω φ₁) (a₂ : admitted D ω φ₂)
    (h : ∀ y t : ℝ, y ≠ 0 →
      (y : ℂ) * Wo D φ (em E (aE (iy y) * rot t)) = (Real.sin t : ℂ) ^ 2 * Wo D φ₀ (em E (aE (iy y) * rot t)) +
        (Real.sin t : ℂ) * (Real.cos t : ℂ) * Wo D φ₁ (em E (aE (iy y) * rot t)) +
        (Real.cos t : ℂ) ^ 2 * Wo D φ₂ (em E (aE (iy y) * rot t)))
    (k : ℕ) (p : MvPolynomial (Fin 2) ℂ) {s : ℂ} (hs : 4 < s.re) :
    Mk D χ (k + 1) φ p s = Mk D χ k φ₀ (p * MvPolynomial.X 0 ^ 2) s +
      (Mk D χ k φ₁ (p * (MvPolynomial.X 0 * MvPolynomial.X 1)) s + Mk D χ k φ₂ (p * MvPolynomial.X 1 ^ 2) s) := by
  simp only [Mk_eq]
  rw [← intervalIntegral.integral_add (ii D hχ a₁ k hs _) (ii D hχ a₂ k hs _),
    ← intervalIntegral.integral_add (ii D hχ a₀ k hs _) ((ii D hχ a₁ k hs _).add (ii D hχ a₂ k hs _))]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by positivity)] at ht
  have hI : ∫ y, G D χ (k + 1) φ s t y = (Real.sin t : ℂ) ^ 2 * (∫ y, G D χ k φ₀ s t y) +
      ((Real.sin t : ℂ) * (Real.cos t : ℂ) * (∫ y, G D χ k φ₁ s t y) +
        (Real.cos t : ℂ) ^ 2 * ∫ y, G D χ k φ₂ s t y) := by
    have i₀ := (G_int D hχ a₀ k hs ht).const_mul ((Real.sin t : ℂ) ^ 2)
    have i₁ := (G_int D hχ a₁ k hs ht).const_mul ((Real.sin t : ℂ) * (Real.cos t : ℂ))
    have i₂ := (G_int D hχ a₂ k hs ht).const_mul ((Real.cos t : ℂ) ^ 2)
    have i₃ : Integrable (fun x => (Real.sin t : ℂ) * (Real.cos t : ℂ) * G D χ k φ₁ s t x +
        (Real.cos t : ℂ) ^ 2 * G D χ k φ₂ s t x) := i₁.add i₂
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂,
      ← integral_add i₀ i₃]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne] with y hy
    simp only [G, pow_succ, Pi.add_apply]
    linear_combination (((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) * h y t hy
  simp only [hI, map_mul, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp
  ring

/- English proof (translation)
Simplify using `[Fin.sum_univ_add, Fin.append_left, Fin.append_right]`.
-/
private theorem merge {α β : Type} {c : α → β → ℂ} {n m : ℕ} (f : Fin n → α) (q : Fin n → β) (f' : Fin m → α) (q' : Fin m → β) :
    ∑ i, c (Fin.append f f' i) (Fin.append q q' i) = ∑ i, c (f i) (q i) + ∑ i, c (f' i) (q' i) := by
  simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

variable [IsTotallyComplex E]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `φ e p hφ hp`. Conclude with `⟨1, fun _ => φ, fun _ => p, fun _ => ⟨hφ, hp⟩, fun s _ => by simp⟩`. Consider the case `succ k ih`.

Introduce `φ e p hφ hp`. Take `⟨φ₀, φ₁, φ₂, g₀, g₁, g₂, h⟩` from `hS φ hφ`. Establish `X0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1` using `MvPolynomial.isHomogeneous_X ℂ 0`. Establish `X1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1` using `MvPolynomial.isHomogeneous_X ℂ 1`. Establish `d₀ : (p * MvPolynomial.X 0 ^ 2).IsHomogeneous (2 * (e + 1))`.

Simplify `hp.mul (X0.pow 2)` using `[mul_add]`. Establish `d₁ : (p * (MvPolynomial.X 0 * MvPolynomial.X 1)).IsHomogeneous (2 * (e + 1))`. Simplify `hp.mul (X0.mul X1)` using `[mul_add]`. Establish `d₂ : (p * MvPolynomial.X 1 ^ 2).IsHomogeneous (2 * (e + 1))`. Simplify `hp.mul (X1.pow 2)` using `[mul_add]`.

Take `⟨n₀, f₀, q₀, c₀, s₀⟩` from `ih φ₀ (e + 1) _ g₀ d₀`. Take `⟨n₁, f₁, q₁, c₁, s₁⟩` from `ih φ₁ (e + 1) _ g₁ d₁`. Take `⟨n₂, f₂, q₂, c₂, s₂⟩` from `ih φ₂ (e + 1) _ g₂ d₂`. Establish `ar : ∀ x : ℕ, 2 * (e + 1 + x) = 2 * (e + (x + 1))` using `fun x => by ring`. Use `⟨n₀ + (n₁ + n₂), Fin.append f₀ (Fin.append f₁ f₂), Fin.append q₀ (Fin.append q₁ q₂), ?_, fun s hs => ?_⟩` and prove the remaining obligations.

Introduce `i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.append_left]`. Conclude with `⟨(c₀ i).1, ar k ▸ (c₀ i).2⟩`. Simplify using `only [Fin.append_right]`.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.append_left]`. Conclude with `⟨(c₁ i).1, ar k ▸ (c₁ i).2⟩`. Simplify using `only [Fin.append_right]`. Conclude with `⟨(c₂ i).1, ar k ▸ (c₂ i).2⟩`.

Rewrite using `[merge (c := fun a b => Mk D χ 0 a b s), merge (c := fun a b => Mk D χ 0 a b s), step D hχ (hA _ g₀.mem) (hA _ g₁.mem) (hA _ g₂.mem) h k p hs, s₀ s hs, s₁ s hs, s₂ s hs]`.
-/
private theorem main (D : Dat ℚ E) {P : CuspSub E 2} {ω χ : HChar ℚ} (hA : ∀ φ ∈ Tr P, admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) {L N : ℕ}
    (hS : ∀ φ, Gd D P L N φ → ∃ φ₀ φ₁ φ₂, Gd D P L N φ₀ ∧ Gd D P L N φ₁ ∧ Gd D P L N φ₂ ∧ ∀ y t : ℝ, y ≠ 0 →
      (y : ℂ) * Wo D φ (em E (aE (iy y) * rot t)) = (Real.sin t : ℂ) ^ 2 * Wo D φ₀ (em E (aE (iy y) * rot t)) +
        (Real.sin t : ℂ) * (Real.cos t : ℂ) * Wo D φ₁ (em E (aE (iy y) * rot t)) +
        (Real.cos t : ℂ) ^ 2 * Wo D φ₂ (em E (aE (iy y) * rot t))) (k : ℕ) :
    ∀ (φ : GL (Fin 2) (A E) → ℂ) (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), Gd D P L N φ → p.IsHomogeneous (2 * e) →
      ∃ (n : ℕ) (f : Fin n → GL (Fin 2) (A E) → ℂ) (q : Fin n → MvPolynomial (Fin 2) ℂ),
        (∀ i, Gd D P L N (f i) ∧ (q i).IsHomogeneous (2 * (e + k))) ∧
        ∀ s : ℂ, 4 < s.re → Mk D χ k φ p s = ∑ i, Mk D χ 0 (f i) (q i) s := by
  induction k with
  | zero =>
    intro φ e p hφ hp
    exact ⟨1, fun _ => φ, fun _ => p, fun _ => ⟨hφ, hp⟩, fun s _ => by simp⟩
  | succ k ih =>
    intro φ e p hφ hp
    obtain ⟨φ₀, φ₁, φ₂, g₀, g₁, g₂, h⟩ := hS φ hφ
    have X0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ 0
    have X1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ 1
    have d₀ : (p * MvPolynomial.X 0 ^ 2).IsHomogeneous (2 * (e + 1)) := by
      simpa [mul_add] using hp.mul (X0.pow 2)
    have d₁ : (p * (MvPolynomial.X 0 * MvPolynomial.X 1)).IsHomogeneous (2 * (e + 1)) := by
      simpa [mul_add] using hp.mul (X0.mul X1)
    have d₂ : (p * MvPolynomial.X 1 ^ 2).IsHomogeneous (2 * (e + 1)) := by
      simpa [mul_add] using hp.mul (X1.pow 2)
    obtain ⟨n₀, f₀, q₀, c₀, s₀⟩ := ih φ₀ (e + 1) _ g₀ d₀
    obtain ⟨n₁, f₁, q₁, c₁, s₁⟩ := ih φ₁ (e + 1) _ g₁ d₁
    obtain ⟨n₂, f₂, q₂, c₂, s₂⟩ := ih φ₂ (e + 1) _ g₂ d₂
    have ar : ∀ x : ℕ, 2 * (e + 1 + x) = 2 * (e + (x + 1)) := fun x => by ring
    refine ⟨n₀ + (n₁ + n₂), Fin.append f₀ (Fin.append f₁ f₂), Fin.append q₀ (Fin.append q₁ q₂), ?_, fun s hs => ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(c₀ i).1, ar k ▸ (c₀ i).2⟩
      · simp only [Fin.append_right]
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left]
          exact ⟨(c₁ i).1, ar k ▸ (c₁ i).2⟩
        · simp only [Fin.append_right]
          exact ⟨(c₂ i).1, ar k ▸ (c₂ i).2⟩
    · rw [merge (c := fun a b => Mk D χ 0 a b s), merge (c := fun a b => Mk D χ 0 a b s),
        step D hχ (hA _ g₀.mem) (hA _ g₁.mem) (hA _ g₂.mem) h k p hs, s₀ s hs, s₁ s hs, s₂ s hs]

/- English proof (translation)
Introduce `hT hS E _ _ _ D P ω χ hC hU hχ L N k φ e p hφ hp`. Establish `hn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1` using `fun a => by`. Establish `h1` using `congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h1`. Rewrite `h1` using `[hU a, mul_one]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1`. Conclude with `main D (hT E D P ω χ hC hU hχ) hn (hS E D P ω χ hC hU hχ L N) k φ e p hφ hp`.
-/
theorem shiftM_of : TrAdm → Shift → ShiftM := by
  intro hT hS E _ _ _ D P ω χ hC hU hχ L N k φ e p hφ hp
  have hn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := fun a => by
    have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h1
    rw [hU a, mul_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  exact main D (hT E D P ω χ hC hU hχ) hn (hS E D P ω χ hC hU hχ L N) k φ e p hφ hp

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
