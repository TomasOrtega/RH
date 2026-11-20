import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

def one1 : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) 1

def pw1 (β : ℝ) : ℝ → ℝ := Set.indicator (Set.Icc (-1) 1) (fun t => |t| ^ (-β))

/- English proof (translation)
Unfold `one1`. Use `first`. Consider the case `exact (continuous_one.integrableOn_Icc).integrable_indicator measurableSet_Icc`. Consider the case `exact (Continuous.integrableOn_Icc continuous_const).integrable_indicator measurableSet_Icc`. Consider the case `exact (integrableOn_const.2 (Or.inr measure_Icc_lt_top)).integrable_indicator measurableSet_Icc`.
-/
lemma integrable_unitIndicator : Integrable one1 := by
  unfold one1
  first
  | exact (continuous_one.integrableOn_Icc).integrable_indicator measurableSet_Icc
  | exact (Continuous.integrableOn_Icc continuous_const).integrable_indicator measurableSet_Icc
  | exact (integrableOn_const.2 (Or.inr measure_Icc_lt_top)).integrable_indicator measurableSet_Icc

/- English proof (translation)
Establish `hr : (-1 : ℝ) < -β` using `by linarith`. Establish `h0 : IntervalIntegrable (fun t : ℝ => t ^ (-β)) volume 0 1` using `by first`. Consider the case `exact intervalIntegral.intervalIntegrable_rpow' hr`. Consider the case `exact intervalIntegrable_rpow' hr`. Establish `hpos : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume 0 1`.

Rewrite `h0`, the goal using `[intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]`. Use `h0.congr_fun (fun t ht => ?_) measurableSet_Ioc` and prove the remaining obligations. Rewrite using `[abs_of_pos ht.1]`. Establish `hneg : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 0`. Rewrite using `[IntervalIntegrable.iff_comp_neg]`.

Simplify `hpos.symm` using `[abs_neg]`. Establish `hall : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 1` using `hneg.trans hpos`. Rewrite `hall` using `[intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]`. Unfold `pw1`. Conclude with `hall.integrable_indicator measurableSet_Icc`.
-/
lemma integrable_powIndicator {β : ℝ} (hβ : β < 1) : Integrable (pw1 β) := by
  have hr : (-1 : ℝ) < -β := by linarith
  have h0 : IntervalIntegrable (fun t : ℝ => t ^ (-β)) volume 0 1 := by
    first
    | exact intervalIntegral.intervalIntegrable_rpow' hr
    | exact intervalIntegrable_rpow' hr
  have hpos : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h0 ⊢
    refine h0.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [abs_of_pos ht.1]
  have hneg : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using hpos.symm
  have hall : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 1 := hneg.trans hpos
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at hall
  unfold pw1
  exact hall.integrable_indicator measurableSet_Icc

/- English proof (translation)
Establish `h : Integrable (fun z : ℝ × ℝ => p z.1 * q z.2) (volume.prod volume)` using `by first`. Consider the case `exact Integrable.mul_prod hp hq`. Consider the case `exact Integrable.prod_mul hp hq`. Consider the case `exact Integrable.prod_smul hp hq`. Establish `e` using `Complex.volume_preserving_equiv_real_prod`.

Establish `h2` using `(e.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).2 h`. Use `first`. Consider the case `exact h2`. Consider the case `(convert h2 using 1; funext z; rfl)`. Consider the case `(convert h2 using 1; funext z; simp [Complex.measurableEquivRealProd])`.
-/
lemma integrable_reim {p q : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q) :
    Integrable (fun z : ℂ => p z.re * q z.im) := by
  have h : Integrable (fun z : ℝ × ℝ => p z.1 * q z.2) (volume.prod volume) := by
    first
    | exact Integrable.mul_prod hp hq
    | exact Integrable.prod_mul hp hq
    | exact Integrable.prod_smul hp hq
  have e := Complex.volume_preserving_equiv_real_prod
  have h2 := (e.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).2 h
  first
  | exact h2
  | (convert h2 using 1; funext z; rfl)
  | (convert h2 using 1; funext z; simp [Complex.measurableEquivRealProd])

/- English proof (translation)
Establish `e` using `Complex.volume_preserving_equiv_real_prod`. Establish `h1 : volume {z : ℂ | z.im = 0} = 0`. Establish `hs : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {0})` using `by first`. Consider the case `(ext z; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)`. Consider the case `(ext z; simp [Complex.measurableEquivRealProd])`.

Rewrite using `[hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]`. Simplify using the standard rewrite rules. Establish `h2 : volume {z : ℂ | z.re = 0} = 0`. Establish `hs : {z : ℂ | z.re = 0} = Complex.measurableEquivRealProd ⁻¹' ({0} ×ˢ Set.univ)` using `by first`. Consider the case `(ext z; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)`.

Consider the case `(ext z; simp [Complex.measurableEquivRealProd])`. Rewrite using `[hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]`. Simplify using the standard rewrite rules. Establish `hu : {z : ℂ | z.im = 0 ∨ z.re = 0} = {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re = 0}` using `rfl`. Rewrite using `[hu]`.

Conclude with `measure_union_null h1 h2`.
-/
lemma volume_axes : volume {z : ℂ | z.im = 0 ∨ z.re = 0} = 0 := by
  have e := Complex.volume_preserving_equiv_real_prod
  have h1 : volume {z : ℂ | z.im = 0} = 0 := by
    have hs : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ {0}) := by
      first
      | (ext z; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h2 : volume {z : ℂ | z.re = 0} = 0 := by
    have hs : {z : ℂ | z.re = 0} = Complex.measurableEquivRealProd ⁻¹' ({0} ×ˢ Set.univ) := by
      first
      | (ext z; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      | (ext z; simp [Complex.measurableEquivRealProd])
    rw [hs, e.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hu : {z : ℂ | z.im = 0 ∨ z.re = 0} = {z : ℂ | z.im = 0} ∪ {z : ℂ | z.re = 0} := rfl
  rw [hu]
  exact measure_union_null h1 h2

/- English proof (translation)
Establish `hs : {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} = ⋃ i, (fun x : ι → ℂ => x i) ⁻¹' {z : ℂ | z.im = 0 ∨ z.re = 0}`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hs]`. Use `measure_iUnion_null fun i => ?_` and prove the remaining obligations.

Rewrite using `[volume_pi]`. Use `first`. Consider the case `exact Measure.pi_eval_preimage_null _ volume_axes`. Consider the case `exact Measure.pi_eval_preimage_null volume_axes`. Consider the case `exact Measure.pi_eval_preimage_null (μ := fun _ => volume) volume_axes`.
-/
lemma volume_bad (ι : Type*) [Fintype ι] :
    volume {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} = 0 := by
  have hs : {x : ι → ℂ | ∃ i, (x i).im = 0 ∨ (x i).re = 0} =
      ⋃ i, (fun x : ι → ℂ => x i) ⁻¹' {z : ℂ | z.im = 0 ∨ z.re = 0} := by
    ext x; simp
  rw [hs]
  refine measure_iUnion_null fun i => ?_
  rw [volume_pi]
  first
  | exact Measure.pi_eval_preimage_null _ volume_axes
  | exact Measure.pi_eval_preimage_null volume_axes
  | exact Measure.pi_eval_preimage_null (μ := fun _ => volume) volume_axes

/- English proof (translation)
Set `L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ)` to `(Matrix.toLin' h).restrictScalars ℝ`. Establish `hfun : (fun y : ι → ℂ => h.mulVec y) = ⇑L`. Use function extensionality and compare the values at `y`. Use `first`. Consider the case `rfl`.

Consider the case `simp [L, Matrix.toLin'_apply]`. Establish `hdetC : Complex.normSq h.det = 1`. Establish `h1` using `congrArg Matrix.det hu`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`. Establish `h2 : ((Complex.normSq h.det : ℝ) : ℂ) = 1`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Use `first`. Consider the case `exact h1`. Consider the case `(rw [starRingEnd_apply]; exact h1)`. Consider the case `simpa using h1`.

Conclude with `h2` after adjusting the coercions. Establish `hdet : LinearMap.det L = 1` using `by first`. Consider the case `(rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])`. Consider the case `(show LinearMap.det ((Matrix.toLin' h).restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])`.

Establish `hmeas : Measurable (fun y : ι → ℂ => h.mulVec y)`. Rewrite using `[hfun]`. Conclude with `L.continuous_of_finiteDimensional.measurable`. Use `⟨hmeas, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`.

Use `first`. Consider the case `(rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]; simp)`. Consider the case `(rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]; simp)`.
-/
lemma mp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) (hu : h.conjTranspose * h = 1) :
    MeasurePreserving (fun y : ι → ℂ => h.mulVec y) volume volume := by
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' h).restrictScalars ℝ
  have hfun : (fun y : ι → ℂ => h.mulVec y) = ⇑L := by
    funext y
    first
    | rfl
    | simp [L, Matrix.toLin'_apply]
  have hdetC : Complex.normSq h.det = 1 := by
    have h1 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
    have h2 : ((Complex.normSq h.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      first
      | exact h1
      | (rw [starRingEnd_apply]; exact h1)
      | simpa using h1
    exact_mod_cast h2
  have hdet : LinearMap.det L = 1 := by
    first
    | (rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
    | (show LinearMap.det ((Matrix.toLin' h).restrictScalars ℝ) = 1
       rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
  have hmeas : Measurable (fun y : ι → ℂ => h.mulVec y) := by
    rw [hfun]
    exact L.continuous_of_finiteDimensional.measurable
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  first
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]; simp)
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]; simp)

section Shell

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tW (q : ι) (x : ι → ℂ) : ℝ := Real.sqrt (∑ i, if i = q then 0 else Complex.normSq (x i))

def Bset (q : ι) : Set (ι → ℂ) := {x | 1 / 2 ≤ tW q x ∧ tW q x ≤ 1 ∧ ‖x q‖ ≤ 1}

def PsiF (p q : ι) (s : ℝ) (x : ι → ℂ) : ℝ≥0∞ := (‖1 - star (x p) / (tW q x : ℂ)‖₊ : ℝ≥0∞) ^ (-s)

def eF (p q i : ι) (z : ℂ) : ℝ := if i = q then 1 else if i = p then |z.im| else |z.re| * |z.im|

def gF (p q : ι) (β : ℝ) (i : ι) (z : ℂ) : ℝ :=
  if i = q then one1 z.re * one1 z.im else if i = p then one1 z.re * pw1 β z.im else pw1 β z.re * pw1 β z.im

/- English proof (translation)
Establish `hs : ∀ i, f i = (if i = q then f i else 0) + (if i = q then 0 else f i)`. Introduce `i`. Apply the tactic sequence `split_ifs <;> simp`. Combine the equalities or inequalities in the displayed calculation. Consider the case `(rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp)`.

Consider the case `simp [Finset.sum_add_distrib]`.
-/
lemma sum_split (q : ι) (f : ι → ℝ) : ∑ i, f i = f q + ∑ i, (if i = q then 0 else f i) := by
  have hs : ∀ i, f i = (if i = q then f i else 0) + (if i = q then 0 else f i) := by
    intro i
    split_ifs <;> simp
  calc ∑ i, f i = ∑ i, ((if i = q then f i else 0) + (if i = q then 0 else f i)) :=
        Finset.sum_congr rfl (fun i _ => hs i)
    _ = f q + ∑ i, (if i = q then 0 else f i) := by
        first
        | (rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp)
        | simp [Finset.sum_add_distrib]

/- English proof (translation)
Establish `hnn : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j))`. Introduce `j _`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `Complex.normSq_nonneg _`.

Unfold `tW`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg hnn)]`. Establish `h1` using `Finset.single_le_sum hnn (Finset.mem_univ i)`. Simplify `h1` using `[hi]`.
-/
lemma normSq_le_tW (q : ι) (x : ι → ℂ) (i : ι) (hi : i ≠ q) : Complex.normSq (x i) ≤ tW q x ^ 2 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  unfold tW
  rw [Real.sq_sqrt (Finset.sum_nonneg hnn)]
  have h1 := Finset.single_le_sum hnn (Finset.mem_univ i)
  simpa [hi] using h1

/- English proof (translation)
Unfold `one1`. Rewrite using `[Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]`. Apply the tactic sequence `try rfl`.
-/
lemma unitIndicator_eq {y : ℝ} (hy : |y| ≤ 1) : one1 y = 1 := by
  unfold one1
  rw [Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]
  try rfl

/- English proof (translation)
Unfold `pw1`. Rewrite using `[Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]`. Apply the tactic sequence `try rfl`.
-/
lemma powIndicator_eq {β y : ℝ} (hy : |y| ≤ 1) : pw1 β y = |y| ^ (-β) := by
  unfold pw1
  rw [Set.indicator_of_mem (show y ∈ Set.Icc (-1 : ℝ) 1 from abs_le.mp hy)]
  try rfl

/- English proof (translation)
Distinguish the cases in `h1 : i = q`. Establish `he : gF p q β i = fun z => one1 z.re * one1 z.im`. Use function extensionality and compare the values at `z`. Simplify using `[gF, h1]`. Rewrite using `[he]`.

Conclude with `integrable_reim integrable_unitIndicator integrable_unitIndicator`. Distinguish the cases in `h2 : i = p`. Establish `h1' : p ≠ q`. Rewrite using `[← h2]`. Conclude with `h1`.

Establish `he : gF p q β i = fun z => one1 z.re * pw1 β z.im`. Use function extensionality and compare the values at `z`. Simplify using `[gF, h2, h1']`. Rewrite using `[he]`. Conclude with `integrable_reim integrable_unitIndicator (integrable_powIndicator hβ)`.

Establish `he : gF p q β i = fun z => pw1 β z.re * pw1 β z.im`. Use function extensionality and compare the values at `z`. Simplify using `[gF, h1, h2]`. Rewrite using `[he]`. Conclude with `integrable_reim (integrable_powIndicator hβ) (integrable_powIndicator hβ)`.
-/
lemma gF_integrable (p q : ι) {β : ℝ} (hβ : β < 1) (i : ι) : Integrable (gF p q β i) := by
  by_cases h1 : i = q
  · have he : gF p q β i = fun z => one1 z.re * one1 z.im := by
      funext z
      simp [gF, h1]
    rw [he]
    exact integrable_reim integrable_unitIndicator integrable_unitIndicator
  · by_cases h2 : i = p
    · have h1' : p ≠ q := by
        rw [← h2]
        exact h1
      have he : gF p q β i = fun z => one1 z.re * pw1 β z.im := by
        funext z
        simp [gF, h2, h1']
      rw [he]
      exact integrable_reim integrable_unitIndicator (integrable_powIndicator hβ)
    · have he : gF p q β i = fun z => pw1 β z.re * pw1 β z.im := by
        funext z
        simp [gF, h1, h2]
      rw [he]
      exact integrable_reim (integrable_powIndicator hβ) (integrable_powIndicator hβ)

end Shell

section Shell2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Take `⟨ht1, ht2, hxq⟩` from `hx`. Establish `htpos : 0 < tW q x` using `by linarith`. Establish `hcoord : ∀ z : ℂ, Complex.normSq z ≤ 1 → |z.re| ≤ 1 ∧ |z.im| ≤ 1`. Introduce `z hz`. Rewrite `hz` using `[Complex.normSq_apply]`.

Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[sq_abs z.re, abs_nonneg z.re, mul_self_nonneg z.im]`. Use polynomial arithmetic with `[sq_abs z.im, abs_nonneg z.im, mul_self_nonneg z.re]`. Establish `hnsq : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2`. Introduce `z`.

Use `first`. Consider the case `exact Complex.normSq_eq_norm_sq z`. Consider the case `(rw [Complex.sq_norm])`. Consider the case `(rw [Complex.normSq_eq_abs, Complex.norm_eq_abs])`. Establish `hsmall : ∀ i, i ≠ q → Complex.normSq (x i) ≤ 1`.

Introduce `i hi`. Establish `h1` using `normSq_le_tW q x i hi`. Use polynomial arithmetic with `[htpos]`. Establish `hqsmall : Complex.normSq (x q) ≤ 1`. Rewrite using `[hnsq]`.

Use polynomial arithmetic with `[norm_nonneg (x q)]`. Establish `hnnj : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j))`. Introduce `j _`. Use `split_ifs`. Conclude with `le_rfl`.

Conclude with `Complex.normSq_nonneg _`. Establish `htsq : tW q x ^ 2 = ∑ j, (if j = q then 0 else Complex.normSq (x j))`. Unfold `tW`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg hnnj)]`. Establish `him : (1 - star (x p) / (tW q x : ℂ)).im = (x p).im / tW q x`.

Simplify using `[Complex.div_ofReal_im]`. Apply the tactic sequence `try ring`. Establish `hA : |(x p).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖`. Establish `h1 : |(1 - star (x p) / (tW q x : ℂ)).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖` using `by first`. Consider the case `exact Complex.abs_im_le_norm _`.

Consider the case `exact Complex.abs_im_le_abs _`. Rewrite `h1` using `[him, abs_div, abs_of_pos htpos]`. Establish `h2 : |(x p).im| ≤ |(x p).im| / tW q x` using `by first`. Consider the case `(rw [le_div_iff₀ htpos]; nlinarith [abs_nonneg (x p).im])`. Consider the case `(rw [le_div_iff htpos]; nlinarith [abs_nonneg (x p).im])`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : ∀ i, i ≠ p → i ≠ q → |(x i).re| * |(x i).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖`. Introduce `i hip hiq`. Establish `hsum : Complex.normSq (x p) + Complex.normSq (x i) ≤ tW q x ^ 2`. Rewrite using `[htsq]`.

Establish `hsub : ∑ j ∈ ({p, i} : Finset ι), (if j = q then 0 else Complex.normSq (x j)) ≤ ∑ j, (if j = q then 0 else Complex.normSq (x j))` using `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnnj j (Finset.mem_univ j))`. Rewrite `hsub` using `[Finset.sum_pair (Ne.symm hip), if_neg hpq, if_neg hiq]`. Conclude with `hsub`. Establish `hw : ‖star (x p) / (tW q x : ℂ)‖ = ‖x p‖ / tW q x`. Rewrite using `[norm_div, norm_star]`.

Use `first`. Consider the case `(rw [Complex.norm_real, Real.norm_of_nonneg htpos.le])`. Consider the case `(simp [abs_of_pos htpos]; done)`. Consider the case `(simp [Complex.abs_of_nonneg htpos.le]; done)`. Establish `htri : ‖(1 : ℂ)‖ - ‖star (x p) / (tW q x : ℂ)‖ ≤ ‖1 - star (x p) / (tW q x : ℂ)‖` using `norm_sub_norm_le _ _`.

Rewrite `htri` using `[norm_one, hw]`. Rewrite `hsum` using `[hnsq (x p)]`. Establish `hre2 : 2 * (|(x i).re| * |(x i).im|) ≤ Complex.normSq (x i)`. Rewrite using `[Complex.normSq_apply]`. Use polynomial arithmetic with `[sq_abs (x i).re, sq_abs (x i).im, sq_nonneg (|(x i).re| - |(x i).im|)]`.

Establish `hr0` using `norm_nonneg (x p)`. Establish `hni` using `Complex.normSq_nonneg (x i)`. Establish `hrt : ‖x p‖ ≤ tW q x` using `by nlinarith`. Establish `hm : |(x i).re| * |(x i).im| ≤ tW q x - ‖x p‖`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hrt) (by linarith : (0 : ℝ) ≤ 2 - tW q x - ‖x p‖)]`.

Establish `hd : ‖x p‖ / tW q x ≤ 1 - tW q x + ‖x p‖` using `by first`. Consider the case `(rw [div_le_iff₀ htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])`. Consider the case `(rw [div_le_iff htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpim : 0 < |(x p).im|` using `abs_pos.2 (hg p).1`.

Establish `hu : 0 < ‖1 - star (x p) / (tW q x : ℂ)‖` using `lt_of_lt_of_le hpim hA`. Establish `hP : PsiF p q s x = ENNReal.ofReal (‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s))`. Unfold `PsiF`. Rewrite using `[← ENNReal.ofReal_rpow_of_pos hu]`. Use `congr 1`.

Use `first`. Consider the case `exact (ofReal_norm_eq_coe_nnnorm _).symm`. Consider the case `(rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm])`. Consider the case `exact (enorm_eq_nnnorm _).symm.trans (ofReal_norm_eq_enorm _).symm`. Consider the case `(simp; rfl)`.

Rewrite using `[hP]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hk0 : (0 : ℝ) < k`. Establish `hk0' : 0 < k` using `by omega`. Conclude with `hk0'` after adjusting the coercions.

Establish `hkne : (k : ℝ) ≠ 0` using `hk0.ne'`. Establish `hβ0 : 0 ≤ s / k` using `div_nonneg hs hk0.le`. Establish `key : ∀ a : ℝ, 0 < a → a ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ → ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ a ^ (-(s / k))`. Introduce `a ha hau`. Use `first`.

Consider the case `exact Real.rpow_le_rpow_of_nonpos ha hau (by linarith)`. Consider the case `(rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]`. Conclude with `inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))`. Consider the case `(rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]`. Conclude with `inv_le_inv_of_le (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))`.

Establish `hfac : ∀ i, i ≠ q → ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ gF p q (s / k) i (x i)`. Introduce `i hiq`. Take `⟨hr1, hi1⟩` from `hcoord (x i) (hsmall i hiq)`. Distinguish the cases in `hip : i = p`. Rewrite `hr1`, `hi1`, the goal using `[hip]`.

Establish `he : gF p q (s / k) p (x p) = |(x p).im| ^ (-(s / k))`. Rewrite using `[show gF p q (s / k) p (x p) = one1 (x p).re * pw1 (s / k) (x p).im by simp [gF, hpq], unitIndicator_eq hr1, powIndicator_eq hi1, one_mul]`. Rewrite using `[he]`. Conclude with `key _ hpim hA`. Establish `he : gF p q (s / k) i (x i) = (|(x i).re| * |(x i).im|) ^ (-(s / k))`.

Rewrite using `[show gF p q (s / k) i (x i) = pw1 (s / k) (x i).re * pw1 (s / k) (x i).im by`. Simplify using `[gF, hiq, hip], powIndicator_eq hr1, powIndicator_eq hi1, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]`. Rewrite using `[he]`. Conclude with `key _ (mul_pos (abs_pos.2 (hg i).2) (abs_pos.2 (hg i).1)) (hB i hip hiq)`. Establish `hq1 : gF p q (s / k) q (x q) = 1`.

Take `⟨hr1, hi1⟩` from `hcoord (x q) hqsmall`. Rewrite using `[show gF p q (s / k) q (x q) = one1 (x q).re * one1 (x q).im by simp [gF], unitIndicator_eq hr1, unitIndicator_eq hi1, one_mul]`. Establish `hsplit` using `Finset.mul_prod_erase Finset.univ (fun i => gF p q (s / k) i (x i)) (Finset.mem_univ q)`. Apply the tactic sequence `try simp only at hsplit`. Rewrite using `[← hsplit, hq1, one_mul]`.

Establish `hcard : (Finset.univ.erase q).card = k`. Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, hk]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_const, hcard, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]`.

Use `congr 1`. Use `first`. Consider the case `(rw [neg_mul, div_mul_cancel₀ _ hkne])`. Consider the case `(rw [neg_mul, div_mul_cancel₀ hkne])`. Consider the case `(field_simp; done)`.

Consider the case `(field_simp; ring)`. Use `_ ≤ ∏ i ∈ Finset.univ.erase q, gF p q (s / k) i (x i) := by`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`. Conclude with `Real.rpow_nonneg hu.le _`.

Introduce `i hi`. Conclude with `hfac i (Finset.ne_of_mem_erase hi)`.
-/
lemma psi_le {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k) {s : ℝ}
    (hs : 0 ≤ s) {x : ι → ℂ} (hx : x ∈ Bset q) (hg : ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0) :
    PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
  classical
  obtain ⟨ht1, ht2, hxq⟩ := hx
  have htpos : 0 < tW q x := by linarith

  have hcoord : ∀ z : ℂ, Complex.normSq z ≤ 1 → |z.re| ≤ 1 ∧ |z.im| ≤ 1 := by
    intro z hz
    rw [Complex.normSq_apply] at hz
    constructor
    · nlinarith [sq_abs z.re, abs_nonneg z.re, mul_self_nonneg z.im]
    · nlinarith [sq_abs z.im, abs_nonneg z.im, mul_self_nonneg z.re]
  have hnsq : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := by
    intro z
    first
    | exact Complex.normSq_eq_norm_sq z
    | (rw [Complex.sq_norm])
    | (rw [Complex.normSq_eq_abs, Complex.norm_eq_abs])
  have hsmall : ∀ i, i ≠ q → Complex.normSq (x i) ≤ 1 := by
    intro i hi
    have h1 := normSq_le_tW q x i hi
    nlinarith [htpos]
  have hqsmall : Complex.normSq (x q) ≤ 1 := by
    rw [hnsq]
    nlinarith [norm_nonneg (x q)]

  have hnnj : ∀ j ∈ Finset.univ, 0 ≤ (if j = q then 0 else Complex.normSq (x j)) := by
    intro j _
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _
  have htsq : tW q x ^ 2 = ∑ j, (if j = q then 0 else Complex.normSq (x j)) := by
    unfold tW
    rw [Real.sq_sqrt (Finset.sum_nonneg hnnj)]
  have him : (1 - star (x p) / (tW q x : ℂ)).im = (x p).im / tW q x := by
    simp [Complex.div_ofReal_im]
    try ring
  have hA : |(x p).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    have h1 : |(1 - star (x p) / (tW q x : ℂ)).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
      first
      | exact Complex.abs_im_le_norm _
      | exact Complex.abs_im_le_abs _
    rw [him, abs_div, abs_of_pos htpos] at h1
    have h2 : |(x p).im| ≤ |(x p).im| / tW q x := by
      first
      | (rw [le_div_iff₀ htpos]; nlinarith [abs_nonneg (x p).im])
      | (rw [le_div_iff htpos]; nlinarith [abs_nonneg (x p).im])
    linarith
  have hB : ∀ i, i ≠ p → i ≠ q → |(x i).re| * |(x i).im| ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ := by
    intro i hip hiq
    have hsum : Complex.normSq (x p) + Complex.normSq (x i) ≤ tW q x ^ 2 := by
      rw [htsq]
      have hsub : ∑ j ∈ ({p, i} : Finset ι), (if j = q then 0 else Complex.normSq (x j)) ≤
          ∑ j, (if j = q then 0 else Complex.normSq (x j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => hnnj j (Finset.mem_univ j))
      rw [Finset.sum_pair (Ne.symm hip), if_neg hpq, if_neg hiq] at hsub
      exact hsub
    have hw : ‖star (x p) / (tW q x : ℂ)‖ = ‖x p‖ / tW q x := by
      rw [norm_div, norm_star]
      first
      | (rw [Complex.norm_real, Real.norm_of_nonneg htpos.le])
      | (simp [abs_of_pos htpos]; done)
      | (simp [Complex.abs_of_nonneg htpos.le]; done)
    have htri : ‖(1 : ℂ)‖ - ‖star (x p) / (tW q x : ℂ)‖ ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, hw] at htri
    rw [hnsq (x p)] at hsum
    have hre2 : 2 * (|(x i).re| * |(x i).im|) ≤ Complex.normSq (x i) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_abs (x i).re, sq_abs (x i).im, sq_nonneg (|(x i).re| - |(x i).im|)]
    have hr0 := norm_nonneg (x p)
    have hni := Complex.normSq_nonneg (x i)
    have hrt : ‖x p‖ ≤ tW q x := by nlinarith
    have hm : |(x i).re| * |(x i).im| ≤ tW q x - ‖x p‖ := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrt) (by linarith : (0 : ℝ) ≤ 2 - tW q x - ‖x p‖)]
    have hd : ‖x p‖ / tW q x ≤ 1 - tW q x + ‖x p‖ := by
      first
      | (rw [div_le_iff₀ htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
      | (rw [div_le_iff htpos]; nlinarith [mul_nonneg (sub_nonneg.2 ht2) (sub_nonneg.2 hrt)])
    linarith
  have hpim : 0 < |(x p).im| := abs_pos.2 (hg p).1
  have hu : 0 < ‖1 - star (x p) / (tW q x : ℂ)‖ := lt_of_lt_of_le hpim hA
  have hP : PsiF p q s x = ENNReal.ofReal (‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)) := by
    unfold PsiF
    rw [← ENNReal.ofReal_rpow_of_pos hu]
    congr 1
    first
    | exact (ofReal_norm_eq_coe_nnnorm _).symm
    | (rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm])
    | exact (enorm_eq_nnnorm _).symm.trans (ofReal_norm_eq_enorm _).symm
    | (simp; rfl)
  rw [hP]
  apply ENNReal.ofReal_le_ofReal
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hβ0 : 0 ≤ s / k := div_nonneg hs hk0.le
  have key : ∀ a : ℝ, 0 < a → a ≤ ‖1 - star (x p) / (tW q x : ℂ)‖ →
      ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ a ^ (-(s / k)) := by
    intro a ha hau
    first
    | exact Real.rpow_le_rpow_of_nonpos ha hau (by linarith)
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
    | (rw [Real.rpow_neg hu.le, Real.rpow_neg ha.le]
       exact inv_le_inv_of_le (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hau hβ0))
  have hfac : ∀ i, i ≠ q → ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) ≤ gF p q (s / k) i (x i) := by
    intro i hiq
    obtain ⟨hr1, hi1⟩ := hcoord (x i) (hsmall i hiq)
    by_cases hip : i = p
    · rw [hip] at hr1 hi1 ⊢
      have he : gF p q (s / k) p (x p) = |(x p).im| ^ (-(s / k)) := by
        rw [show gF p q (s / k) p (x p) = one1 (x p).re * pw1 (s / k) (x p).im by simp [gF, hpq],
          unitIndicator_eq hr1, powIndicator_eq hi1, one_mul]
      rw [he]
      exact key _ hpim hA
    · have he : gF p q (s / k) i (x i) = (|(x i).re| * |(x i).im|) ^ (-(s / k)) := by
        rw [show gF p q (s / k) i (x i) = pw1 (s / k) (x i).re * pw1 (s / k) (x i).im by
          simp [gF, hiq, hip], powIndicator_eq hr1, powIndicator_eq hi1, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [he]
      exact key _ (mul_pos (abs_pos.2 (hg i).2) (abs_pos.2 (hg i).1)) (hB i hip hiq)
  have hq1 : gF p q (s / k) q (x q) = 1 := by
    obtain ⟨hr1, hi1⟩ := hcoord (x q) hqsmall
    rw [show gF p q (s / k) q (x q) = one1 (x q).re * one1 (x q).im by simp [gF], unitIndicator_eq hr1, unitIndicator_eq hi1, one_mul]
  have hsplit := Finset.mul_prod_erase Finset.univ (fun i => gF p q (s / k) i (x i)) (Finset.mem_univ q)
  try simp only at hsplit
  rw [← hsplit, hq1, one_mul]
  have hcard : (Finset.univ.erase q).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, hk]
    simp
  calc ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-s)
      = ∏ i ∈ Finset.univ.erase q, ‖1 - star (x p) / (tW q x : ℂ)‖ ^ (-(s / k)) := by
        rw [Finset.prod_const, hcard, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
        congr 1
        first
        | (rw [neg_mul, div_mul_cancel₀ _ hkne])
        | (rw [neg_mul, div_mul_cancel₀ hkne])
        | (field_simp; done)
        | (field_simp; ring)
    _ ≤ ∏ i ∈ Finset.univ.erase q, gF p q (s / k) i (x i) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Real.rpow_nonneg hu.le _
        · intro i hi
          exact hfac i (Finset.ne_of_mem_erase hi)

/- English proof (translation)
Establish `hc : Continuous (tW q)`. Unfold `tW`. Use `Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : i = q`. Simplify using `only [h, if_true]`.

Conclude with `continuous_const`. Simplify using `only [h, if_false]`. Conclude with `Complex.continuous_normSq.comp (continuous_apply i)`. Establish `hn : Continuous (fun x : ι → ℂ => ‖x q‖)` using `continuous_norm.comp (continuous_apply q)`. Unfold `Bset`.

Conclude with `(measurableSet_le measurable_const hc.measurable).inter ((measurableSet_le hc.measurable measurable_const).inter (measurableSet_le hn.measurable measurable_const))`.
-/
lemma measurableSet_Bset (q : ι) : MeasurableSet (Bset q) := by
  have hc : Continuous (tW q) := by
    unfold tW
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    by_cases h : i = q
    · simp only [h, if_true]
      exact continuous_const
    · simp only [h, if_false]
      exact Complex.continuous_normSq.comp (continuous_apply i)
  have hn : Continuous (fun x : ι → ℂ => ‖x q‖) := continuous_norm.comp (continuous_apply q)
  unfold Bset
  exact (measurableSet_le measurable_const hc.measurable).inter
    ((measurableSet_le hc.measurable measurable_const).inter
      (measurableSet_le hn.measurable measurable_const))

/- English proof (translation)
Use `first`. Consider the case `exact Integrable.fintype_prod (f := fun i => gF p q β i) (fun i => gF_integrable p q hβ i)`. Consider the case `exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i)`. Consider the case `(rw [volume_pi]; exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i))`. Consider the case `exact Integrable.fintype_prod_dep (fun i => gF_integrable p q hβ i)`.
-/
lemma integrable_gprod (p q : ι) {β : ℝ} (hβ : β < 1) :
    Integrable (fun x : ι → ℂ => ∏ i, gF p q β i (x i)) := by
  first
  | exact Integrable.fintype_prod (f := fun i => gF p q β i) (fun i => gF_integrable p q hβ i)
  | exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i)
  | (rw [volume_pi]; exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i))
  | exact Integrable.fintype_prod_dep (fun i => gF_integrable p q hβ i)

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `h` using `volume_bad ι`. Use `h using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, not_forall, not_and_or, ne_eq, not_not]`.
-/
lemma ae_good : ∀ᵐ x : ι → ℂ, ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0 := by
  rw [ae_iff]
  have h := volume_bad ι
  convert h using 2
  ext x
  simp only [Set.mem_setOf_eq, not_forall, not_and_or, ne_eq, not_not]

/- English proof (translation)
Establish `hk0 : (0 : ℝ) < k`. Establish `hk0' : 0 < k` using `by omega`. Conclude with `hk0'` after adjusting the coercions. Establish `hβ : s / k < 1`. Rewrite using `[div_lt_one hk0]`.

Conclude with `hsk`. Establish `hG` using `integrable_gprod p q hβ`. Establish `hae : ∀ᵐ x : ι → ℂ, x ∈ Bset q → PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i))` using `by filter_upwards [ae_good] with x hg hx`. Conclude with `psi_le hpq hk hk1 hs hx hg`. Establish `h1 : ∫⁻ x in Bset q, PsiF p q s x ≤ ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i))` using `lintegral_mono_ae ((ae_restrict_iff' (measurableSet_Bset q)).2 hae)`.

Establish `h2 : ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) ≤ ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i))` using `setLIntegral_le_lintegral _ _`. Establish `h3 : ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) < ∞` using `by first`. Consider the case `exact Integrable.lintegral_lt_top hG`. Consider the case `exact HasFiniteIntegral.lintegral_lt_top hG.2`. Conclude with `lt_of_le_of_lt (h1.trans h2) h3`.
-/
lemma lint_Bset_lt_top {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k)
    {s : ℝ} (hs : 0 ≤ s) (hsk : s < k) : ∫⁻ x in Bset q, PsiF p q s x < ∞ := by
  have hk0 : (0 : ℝ) < k := by
    have hk0' : 0 < k := by omega
    exact_mod_cast hk0'
  have hβ : s / k < 1 := by
    rw [div_lt_one hk0]
    exact hsk
  have hG := integrable_gprod p q hβ
  have hae : ∀ᵐ x : ι → ℂ, x ∈ Bset q →
      PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by
    filter_upwards [ae_good] with x hg hx
    exact psi_le hpq hk hk1 hs hx hg
  have h1 : ∫⁻ x in Bset q, PsiF p q s x ≤
      ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    lintegral_mono_ae ((ae_restrict_iff' (measurableSet_Bset q)).2 hae)
  have h2 : ∫⁻ x in Bset q, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) ≤
      ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) :=
    setLIntegral_le_lintegral _ _
  have h3 : ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) < ∞ := by
    first
    | exact Integrable.lintegral_lt_top hG
    | exact HasFiniteIntegral.lintegral_lt_top hG.2
  exact lt_of_le_of_lt (h1.trans h2) h3

end Shell2

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
