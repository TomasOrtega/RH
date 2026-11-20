import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjectionPullbackZeroSetNull
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIsolFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Minor

variable {Ω : Type} [Fintype Ω]

def minorRatio (b a : Ω → ℂ) : ℝ :=
  ‖fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1‖ / ‖a‖

/- English proof (translation)
The claim follows from `div_nonneg (norm_nonneg _) (norm_nonneg _)`.
-/
theorem minorRatio_nonneg (b a : Ω → ℂ) : 0 ≤ minorRatio b a :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

/- English proof (translation)
Unfold `minorRatio`. Establish `h : (fun il : Ω × Ω => (μ • a) il.1 * b il.2 - (μ • a) il.2 * b il.1) = μ • fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1`. Use function extensionality and compare the values at `il`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, norm_smul, norm_smul]`. Conclude with `mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hμ)`.
-/
theorem minorRatio_smul (b a : Ω → ℂ) {μ : ℂ} (hμ : μ ≠ 0) : minorRatio b (μ • a) = minorRatio b a := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => (μ • a) il.1 * b il.2 - (μ • a) il.2 * b il.1) =
      μ • fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1 := by
    funext il
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, norm_smul, norm_smul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hμ)

/- English proof (translation)
Unfold `minorRatio`. Establish `h : (fun il : Ω × Ω => b il.1 * b il.2 - b il.2 * b il.1) = 0`. Use function extensionality and compare the values at `il`. Simplify using `only [Pi.zero_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, norm_zero, zero_div]`.
-/
theorem minorRatio_self (b : Ω → ℂ) : minorRatio b b = 0 := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => b il.1 * b il.2 - b il.2 * b il.1) = 0 := by
    funext il
    simp only [Pi.zero_apply]
    ring
  rw [h, norm_zero, zero_div]

/- English proof (translation)
Unfold `minorRatio`. Use `ContinuousAt.div ?_ continuous_norm.continuousAt (norm_ne_zero_iff.mpr ha)` and prove the remaining obligations. Use `(continuous_norm.comp (continuous_pi fun il => ?_)).continuousAt` and prove the remaining obligations. Conclude with `((continuous_apply il.1).mul continuous_const).sub ((continuous_apply il.2).mul continuous_const)`.
-/
theorem continuousAt_minorRatio (b : Ω → ℂ) {a : Ω → ℂ} (ha : a ≠ 0) :
    ContinuousAt (minorRatio b) a := by
  unfold minorRatio
  refine ContinuousAt.div ?_ continuous_norm.continuousAt (norm_ne_zero_iff.mpr ha)
  refine (continuous_norm.comp (continuous_pi fun il => ?_)).continuousAt
  exact ((continuous_apply il.1).mul continuous_const).sub ((continuous_apply il.2).mul continuous_const)

/- English proof (translation)
Unfold `minorRatio at h`. Rewrite `h` using `[div_eq_zero_iff, or_iff_left (norm_ne_zero_iff.mpr ha), norm_eq_zero]`. Establish `hm : ∀ i l, a i * b l = a l * b i` using `fun i l => by`. Use `congrFun h (i, l)` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`.

Conclude with `sub_eq_zero.mp this`. Choose the witnesses or unpack the hypotheses as in `⟨l0, hl0⟩ : ∃ l0, b l0 ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hb (funext hc)`.

Establish `heq : a = (a l0 / b l0) • b`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hl0]`. Conclude with `hm i l0`.

Use `⟨a l0 / b l0, fun h0 => ha ?_, heq⟩` and prove the remaining obligations. Rewrite using `[heq, h0, zero_smul]`.
-/
theorem eq_smul_of_minorRatio {b a : Ω → ℂ} (hb : b ≠ 0) (ha : a ≠ 0) (h : minorRatio b a = 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ a = μ • b := by
  unfold minorRatio at h
  rw [div_eq_zero_iff, or_iff_left (norm_ne_zero_iff.mpr ha), norm_eq_zero] at h
  have hm : ∀ i l, a i * b l = a l * b i := fun i l => by
    have := congrFun h (i, l)
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  obtain ⟨l0, hl0⟩ : ∃ l0, b l0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hb (funext hc)
  have heq : a = (a l0 / b l0) • b := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hl0]
    exact hm i l0
  refine ⟨a l0 / b l0, fun h0 => ha ?_, heq⟩
  rw [heq, h0, zero_smul]

end Minor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
The claim follows from `continuous_pi fun _ => continuous_finsetProd _ fun _ _ => continuous_apply _`.
-/
theorem continuous_segre : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
  continuous_pi fun _ => continuous_finsetProd _ fun _ _ => continuous_apply _

/- English proof (translation)
Use `choose p hp using hz`. Introduce `h`. Use `congrFun h p` as an intermediate fact. Simplify using `only [segre, Pi.zero_apply] at this`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun k _ => hp k) this`.
-/
theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : segre z ≠ 0 := by
  choose p hp using hz
  intro h
  have := congrFun h p
  simp only [segre, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) this

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

/- English proof (translation)
Take `⟨j, hj⟩` from `R.A.cover x`. Establish `hu : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U x⟩`. Establish `h1 : ContinuousAt (fun x' => R.lift x ((R.A.chart j).symm (R.A.chart j x'))) x` using `ContinuousAt.comp (f := R.A.chart j) (g := fun w => R.lift x ((R.A.chart j).symm w)) (analyticAt_lift_chart R x j hu).continuousAt ((R.A.chart j).continuousAt hj)`. Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with x' hx'`.

Rewrite using `[(R.A.chart j).left_inv hx']`.
-/
theorem continuousAt_lift (x : R.X) : ContinuousAt (fun x' => R.lift x x') x := by
  obtain ⟨j, hj⟩ := R.A.cover x
  have hu : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U x⟩
  have h1 : ContinuousAt (fun x' => R.lift x ((R.A.chart j).symm (R.A.chart j x'))) x :=
    ContinuousAt.comp (f := R.A.chart j) (g := fun w => R.lift x ((R.A.chart j).symm w))
      (analyticAt_lift_chart R x j hu).continuousAt ((R.A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with x' hx'
  rw [(R.A.chart j).left_inv hx']

/- English proof (translation)
Use `continuous_iff_continuousAt.mpr fun x' => ?_` and prove the remaining obligations. Establish `hne : segre (R.lift x' x') ≠ 0` using `segre_ne_zero (R.mem x' x' (R.mem_U x')).1`. Establish `h1 : ContinuousAt (fun x'' => minorRatio b (segre (R.lift x' x''))) x'` using `ContinuousAt.comp (g := minorRatio b) (continuousAt_minorRatio b hne) (continuous_segre.continuousAt.comp (continuousAt_lift R x'))`. Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [(R.isOpen_U x').mem_nhds (R.mem_U x')] with x'' hx''`.

Take `⟨μ, hμ, hμeq⟩` from `segre_of_sameOrbit (R.compat x'' x' x'' ⟨R.mem_U x'', hx''⟩)`. Rewrite using `[hμeq, minorRatio_smul b _ hμ]`.
-/
theorem continuous_minorRatio_lift [DecidableEq K'] (b : ((k : K') → ι' k) → ℂ) :
    Continuous (fun x' : R.X => minorRatio b (segre (R.lift x' x'))) := by
  refine continuous_iff_continuousAt.mpr fun x' => ?_
  have hne : segre (R.lift x' x') ≠ 0 := segre_ne_zero (R.mem x' x' (R.mem_U x')).1
  have h1 : ContinuousAt (fun x'' => minorRatio b (segre (R.lift x' x''))) x' :=
    ContinuousAt.comp (g := minorRatio b) (continuousAt_minorRatio b hne)
      (continuous_segre.continuousAt.comp (continuousAt_lift R x'))
  refine h1.congr ?_
  filter_upwards [(R.isOpen_U x').mem_nhds (R.mem_U x')] with x'' hx''
  obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (R.compat x'' x' x'' ⟨R.mem_U x'', hx''⟩)
  rw [hμeq, minorRatio_smul b _ hμ]

/- English proof (translation)
Establish `hxB : R.lift x x ∉ mcPts J'` using `fun h => hx (Or.inl (Or.inl h))`. Establish `hz'` using `R.mem x x (R.mem_U x)`. Take `⟨j, hj⟩` from `R.A.cover x`. Establish `hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧ LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0`. Assume the negation of the conclusion as `h`.

Conclude with `hx (Or.inr ⟨j, hj, h⟩)`. Take `⟨e, he⟩` from `hasStrictFDerivAt_equiv hgood.1 hgood.2`. Establish `hinj` using `(he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).injOn`. Use `set V := (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).source with hVdef`. Establish `hVo : IsOpen V` using `(R.A.chart j).isOpen_inter_preimage (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).open_source`.

Establish `hxV : x ∈ V` using `⟨hj, he.mem_toOpenPartialHomeomorph_source⟩`. Establish `hb : segre (R.lift x x) ≠ 0` using `segre_ne_zero hz'.1`. Establish `hθc` using `continuous_minorRatio_lift R (segre (R.lift x x))`. Establish `hθpos : ∀ x' ∈ Vᶜ, 0 < minorRatio (segre (R.lift x x)) (segre (R.lift x' x'))`. Introduce `x' hx'`.

Use `lt_of_le_of_ne (minorRatio_nonneg _ _) (Ne.symm fun h0 => hx' ?_)` and prove the remaining obligations. Take `⟨μ, hμ, hμeq⟩` from `eq_smul_of_minorRatio hb (segre_ne_zero (R.mem x' x' (R.mem_U x')).1) h0`. Establish `hso : SameOrbit (R.lift x' x') (R.lift x x)` using `sameOrbit_of_segre hz'.1 μ hμ hμeq`. Rewrite using `[← R.inj x x' hxB (sameOrbit_comm hso)]`. Conclude with `hxV`.

Choose the witnesses or unpack the hypotheses as in `⟨m0, hm0, hm0le⟩ : ∃ m0 : ℝ, 0 < m0 ∧ ∀ x' ∈ Vᶜ, m0 ≤ minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by`. Break down `(Vᶜ).eq_empty_or_nonempty with hC | hC` into its components or cases. Conclude with `⟨1, one_pos, fun x' hx' => by rw [hC] at hx'; exact absurd hx' (Set.notMem_empty x')⟩`. Take `⟨x1, hx1, hmin⟩` from `(hVo.isClosed_compl.isCompact).exists_isMinOn hC hθc.continuousOn`. Conclude with `⟨_, hθpos x1 hx1, fun x' hx' => isMinOn_iff.mp hmin x' hx'⟩`.

Establish `hDc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => minorRatio (segre (R.lift x x)) (segre z)) (R.lift x x)` using `ContinuousAt.comp (g := minorRatio (segre (R.lift x x))) (continuousAt_minorRatio _ hb) continuous_segre.continuousAt`. Take `⟨ε1, hε1, hball1⟩` from `Metric.continuousAt_iff.mp hDc m0 hm0`. Choose the witnesses or unpack the hypotheses as in `⟨g, hgJ, hg0⟩ : ∃ g ∈ J', eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hxB ⟨hz'.1, h⟩`. Establish `hgc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => eval z (map (Int.castRingHom ℂ) g)) (R.lift x x)` using `(MvPolynomial.continuous_eval _).continuousAt`. Take `⟨ε2, hε2, hball2⟩` from `Metric.continuousAt_iff.mp hgc _ (norm_pos_iff.mpr hg0)`. Use `⟨min ε1 ε2, lt_min hε1 hε2, fun z'' hz'' hzv hd => ?_⟩` and prove the remaining obligations. Establish `hd1 : dist z'' (R.lift x x) < ε1` using `lt_of_lt_of_le hd (min_le_left _ _)`.

Establish `hd2 : dist z'' (R.lift x x) < ε2` using `lt_of_lt_of_le hd (min_le_right _ _)`. Establish `hzB : z'' ∉ mcPts J'`. Introduce `h`. Establish `h2 : dist (eval z'' (map (Int.castRingHom ℂ) g)) (eval (R.lift x x) (map (Int.castRingHom ℂ) g)) < ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖` using `hball2 hd2`. Rewrite `h2` using `[h.2 g hgJ, dist_zero_left]`.

Conclude with `lt_irrefl _ h2`. Take `⟨x'', hx''⟩` from `R.surj z'' hz'' hzB`. Establish `hθx'' : minorRatio (segre (R.lift x x)) (segre (R.lift x'' x'')) < m0`. Take `⟨μ, hμ, hμeq⟩` from `segre_of_sameOrbit hx''`. Establish `h1 : dist (minorRatio (segre (R.lift x x)) (segre z'')) (minorRatio (segre (R.lift x x)) (segre (R.lift x x))) < m0` using `hball1 hd1`.

Rewrite `h1` using `[minorRatio_self, Real.dist_eq, sub_zero]`. Rewrite using `[hμeq, minorRatio_smul _ _ hμ]`. Conclude with `lt_of_le_of_lt (le_abs_self _) h1`. Establish `hx''V : x'' ∈ V`. Assume the negation of the conclusion as `hc`.

Conclude with `absurd (hm0le x'' hc) (not_le.mpr hθx'')`. Establish `hso : SameOrbit (pullPt R v x'') (pullPt R v x)` using `sameOrbit_tr (sameOrbit_comp hv hx'') hzv`. Establish `hq : pullQ R v Ψ x'' = pullQ R v Ψ x`. Take `⟨μ, hμ, hμeq⟩` from `segre_of_sameOrbit hso`. Use function extensionality and compare the values at `i`.

Simplify using `only [pullQ, hμeq, map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_div_mul_left _ _ hμ`. Establish `hxx : x'' = x`. Establish `h1 : (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x'') = (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x)`. Simplify using `only [Function.comp_apply, (R.A.chart j).left_inv hx''V.1, (R.A.chart j).left_inv hj, hq]`.

Establish `h2 : R.A.chart j x'' = R.A.chart j x` using `hinj hx''V.2 hxV.2 (by rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; exact h1)`. Conclude with `(R.A.chart j).injOn hx''V.1 hj h2`. Rewrite `hx''` using `[hxx]`. Conclude with `sameOrbit_comm hx''`.
-/
theorem isolated_of_not_pullBad (hv : IsBlockMap κ v)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X} (hx : x ∉ pullBad R v Ψ) :
    ∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) (pullPt R v x) →
      dist z'' (R.lift x x) < ε → SameOrbit z'' (R.lift x x) := by
  classical
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have hz' := R.mem x x (R.mem_U x)
  obtain ⟨j, hj⟩ := R.A.cover x
  have hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hgood.1 hgood.2
  have hinj := (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).injOn
  set V := (R.A.chart j).source ∩
    (R.A.chart j) ⁻¹' (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).source with hVdef
  have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage
    (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).open_source
  have hxV : x ∈ V := ⟨hj, he.mem_toOpenPartialHomeomorph_source⟩
  have hb : segre (R.lift x x) ≠ 0 := segre_ne_zero hz'.1
  have hθc := continuous_minorRatio_lift R (segre (R.lift x x))
  have hθpos : ∀ x' ∈ Vᶜ, 0 < minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    intro x' hx'
    refine lt_of_le_of_ne (minorRatio_nonneg _ _) (Ne.symm fun h0 => hx' ?_)
    obtain ⟨μ, hμ, hμeq⟩ := eq_smul_of_minorRatio hb (segre_ne_zero (R.mem x' x' (R.mem_U x')).1) h0
    have hso : SameOrbit (R.lift x' x') (R.lift x x) := sameOrbit_of_segre hz'.1 μ hμ hμeq
    rw [← R.inj x x' hxB (sameOrbit_comm hso)]
    exact hxV
  obtain ⟨m0, hm0, hm0le⟩ : ∃ m0 : ℝ, 0 < m0 ∧
      ∀ x' ∈ Vᶜ, m0 ≤ minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    rcases (Vᶜ).eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, fun x' hx' => by rw [hC] at hx'; exact absurd hx' (Set.notMem_empty x')⟩
    · obtain ⟨x1, hx1, hmin⟩ := (hVo.isClosed_compl.isCompact).exists_isMinOn hC hθc.continuousOn
      exact ⟨_, hθpos x1 hx1, fun x' hx' => isMinOn_iff.mp hmin x' hx'⟩
  have hDc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => minorRatio (segre (R.lift x x)) (segre z))
      (R.lift x x) :=
    ContinuousAt.comp (g := minorRatio (segre (R.lift x x))) (continuousAt_minorRatio _ hb)
      continuous_segre.continuousAt
  obtain ⟨ε1, hε1, hball1⟩ := Metric.continuousAt_iff.mp hDc m0 hm0
  obtain ⟨g, hgJ, hg0⟩ : ∃ g ∈ J', eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    by_contra h
    push Not at h
    exact hxB ⟨hz'.1, h⟩
  have hgc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => eval z (map (Int.castRingHom ℂ) g))
      (R.lift x x) :=
    (MvPolynomial.continuous_eval _).continuousAt
  obtain ⟨ε2, hε2, hball2⟩ := Metric.continuousAt_iff.mp hgc _ (norm_pos_iff.mpr hg0)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun z'' hz'' hzv hd => ?_⟩
  have hd1 : dist z'' (R.lift x x) < ε1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist z'' (R.lift x x) < ε2 := lt_of_lt_of_le hd (min_le_right _ _)
  have hzB : z'' ∉ mcPts J' := by
    intro h
    have h2 : dist (eval z'' (map (Int.castRingHom ℂ) g)) (eval (R.lift x x) (map (Int.castRingHom ℂ) g)) <
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ := hball2 hd2
    rw [h.2 g hgJ, dist_zero_left] at h2
    exact lt_irrefl _ h2
  obtain ⟨x'', hx''⟩ := R.surj z'' hz'' hzB
  have hθx'' : minorRatio (segre (R.lift x x)) (segre (R.lift x'' x'')) < m0 := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hx''
    have h1 : dist (minorRatio (segre (R.lift x x)) (segre z''))
        (minorRatio (segre (R.lift x x)) (segre (R.lift x x))) < m0 := hball1 hd1
    rw [minorRatio_self, Real.dist_eq, sub_zero] at h1
    rw [hμeq, minorRatio_smul _ _ hμ]
    exact lt_of_le_of_lt (le_abs_self _) h1
  have hx''V : x'' ∈ V := by
    by_contra hc
    exact absurd (hm0le x'' hc) (not_le.mpr hθx'')
  have hso : SameOrbit (pullPt R v x'') (pullPt R v x) :=
    sameOrbit_tr (sameOrbit_comp hv hx'') hzv
  have hq : pullQ R v Ψ x'' = pullQ R v Ψ x := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hso
    funext i
    simp only [pullQ, hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hμ
  have hxx : x'' = x := by
    have h1 : (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x'') =
        (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
      simp only [Function.comp_apply, (R.A.chart j).left_inv hx''V.1, (R.A.chart j).left_inv hj, hq]
    have h2 : R.A.chart j x'' = R.A.chart j x :=
      hinj hx''V.2 hxV.2 (by rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; exact h1)
    exact (R.A.chart j).injOn hx''V.1 hj h2
  rw [hxx] at hx''
  exact sameOrbit_comm hx''

/- English proof (translation)
Establish `hF` using `fibreFinite K ι (imageZ v P') n Ψ hP hΨ y`. Use `choose! uw huw using fun w (hw : w ∈ fibre (imageZ v P') Ψ y) => hw`. Use `choose T hT using fun w => hIsol K ι K' ι' κ v P' n hv hP' (uw w)`. Use `(hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ => (orbit_subsingleton R t).finite).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hqx, hx⟩`.

Establish `hxB : R.lift x x ∉ mcPts J'` using `fun h => hx (Or.inl (Or.inl h))`. Establish `h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0` using `fun h => hx (Or.inl (Or.inr h))`. Establish `hw` using `IntersectionWithSection.pullW_mem_fibre hv hP R Ψ h0x`. Rewrite `hw` using `[show pullQ R v Ψ x = y from hqx]`. Take `⟨hu1, hu2, -⟩` from `huw _ hw`.

Establish `hso : SameOrbit (pullPt R v x) (uw (pullW R v Ψ x))` using `sameOrbit_of_segre hu1.1 (Ψ (segre (pullPt R v x)) 0) h0x (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])`. Take `⟨ε, hε, hiso⟩` from `isolated_of_not_pullBad R hv Ψ hx`. Take `⟨t, ht, hxt⟩` from `hT (pullW R v Ψ x) (R.lift x x) (R.mem x x (R.mem_U x)) hso ⟨ε, hε, fun z'' hz'' hzu hd => hiso z'' hz'' (sameOrbit_tr hzu (sameOrbit_comm hso)) hd⟩`. Conclude with `Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)`.
-/
theorem pullFib_finite (hIsol : FibreIsolFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (y : Fin n → ℂ) : (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite := by
  classical
  have hF := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  choose! uw huw using fun w (hw : w ∈ fibre (imageZ v P') Ψ y) => hw
  choose T hT using fun w => hIsol K ι K' ι' κ v P' n hv hP' (uw w)
  refine (hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_
  rintro x ⟨hqx, hx⟩
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Ψ h0x
  rw [show pullQ R v Ψ x = y from hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Ψ x)) :=
    sameOrbit_of_segre hu1.1 (Ψ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨ε, hε, hiso⟩ := isolated_of_not_pullBad R hv Ψ hx
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Ψ x) (R.lift x x) (R.mem x x (R.mem_U x)) hso
    ⟨ε, hε, fun z'' hz'' hzu hd => hiso z'' hz'' (sameOrbit_tr hzu (sameOrbit_comm hso)) hd⟩
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
