import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralBoundScaledPotentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshExtensionOffClosedSetStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ShellMass

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

/- English proof (translation)
Take `⟨W, hWo, hyW, G, hG, hGeq⟩` from `hP.2 ((A.chart j).symm y) x ((A.chart j).symm y) ⟨P.mem_U _, hx⟩`. Establish `hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U ((A.chart j).symm y) ∩ P.U x))` using `(A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U _)).inter (P.isOpen_U x))`. Establish `hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U ((A.chart j).symm y) ∩ P.U x)` using `⟨hy, ⟨⟨hyW, P.mem_U _⟩, hx⟩⟩`. Establish `hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y` using `hG j y ⟨hy, hyW⟩`. Establish `hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y`.

Use `(Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `h1 : (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) =ᶠ[nhds y] (fun w => (P.φ x ∘ (A.chart j).symm) w + 1 * ((G ∘ (A.chart j).symm) w).re)` using `by filter_upwards [hVo.mem_nhds hyV] with w hw`. Use `hGeq ((A.chart j).symm w) hw.2` as an intermediate fact. Simplify using `only [Function.comp_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `leviAt`. Rewrite using `[levi_congr h1, levi_add_smul 1 (potSmoothAt A P hP x j ⟨hy, hx⟩) hRe, levi_re_analytic hGa]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_base {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w = leviAt A P j y w := by
  obtain ⟨W, hWo, hyW, G, hG, hGeq⟩ :=
    hP.2 ((A.chart j).symm y) x ((A.chart j).symm y) ⟨P.mem_U _, hx⟩
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ P.U ((A.chart j).symm y) ∩ P.U x)) :=
    (A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U _)).inter (P.isOpen_U x))
  have hyV : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ P.U ((A.chart j).symm y) ∩ P.U x) := ⟨hy, ⟨⟨hyW, P.mem_U _⟩, hx⟩⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ (A.chart j).symm) z).re) y := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have h1 : (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) =ᶠ[nhds y]
      (fun w => (P.φ x ∘ (A.chart j).symm) w + 1 * ((G ∘ (A.chart j).symm) w).re) := by
    filter_upwards [hVo.mem_nhds hyV] with w hw
    have := hGeq ((A.chart j).symm w) hw.2
    simp only [Function.comp_apply]
    linarith
  unfold leviAt
  rw [levi_congr h1, levi_add_smul 1 (potSmoothAt A P hP x j ⟨hy, hx⟩) hRe, levi_re_analytic hGa]
  ring

/- English proof (translation)
The claim follows from `((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le (WithTop.coe_le_coe.2 le_top)`.
-/
theorem smoothOn_contDiffAt {U : Set X} (hU : IsOpen U) {u : X → ℝ} (hu : A.SmoothOn U u) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
  ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hy, hyU⟩)).of_le
    (WithTop.coe_le_coe.2 le_top)

/- English proof (translation)
Introduce `x hx`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Take `⟨j, hj⟩` from `A.cover x`. Establish `h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x)` using `(smoothOn_contDiffAt hU hu j ((A.chart j).map_source hj) (by rw [(A.chart j).left_inv hj]; exact hx)).continuousAt`. Establish `h3 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x` using `h2.comp ((A.chart j).continuousAt hj)`.

Use `h3.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz`. Simplify using `[(A.chart j).left_inv hz]`.
-/
theorem smoothOn_continuousOn {U : Set X} (hU : IsOpen U) {u : X → ℝ} (hu : A.SmoothOn U u) :
    ContinuousOn u U := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨j, hj⟩ := A.cover x
  have h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    (smoothOn_contDiffAt hU hu j ((A.chart j).map_source hj)
      (by rw [(A.chart j).left_inv hj]; exact hx)).continuousAt
  have h3 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h2.comp ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

/- English proof (translation)
Establish `h` using `levi_add_smul 1 (potSmoothAt A P hP x j ⟨hy, hx⟩) hu w`. Rewrite `h` using `[levi_base hP x j hy hx, one_mul]`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Simplify using the standard rewrite rules.
-/
theorem levi_add_fun {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) {u : X → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    levi ((fun z => P.φ x z + u z) ∘ (A.chart j).symm) y w =
      leviAt A P j y w + levi (u ∘ (A.chart j).symm) y w := by
  have h := levi_add_smul 1 (potSmoothAt A P hP x j ⟨hy, hx⟩) hu w
  rw [levi_base hP x j hy hx, one_mul] at h
  rw [← h]
  congr 1
  funext z
  simp

/- English proof (translation)
The claim follows from `levi_add_fun hP _ j hy (P.mem_U _) hu w`.
-/
theorem leviAt_add_ofFun {P : LocPot X} (hP : IsPotential A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {u : X → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y) (w : Fin e → ℂ) :
    leviAt A (P + LocPot.ofFun u) j y w = leviAt A P j y w + levi (u ∘ (A.chart j).symm) y w :=
  levi_add_fun hP _ j hy (P.mem_U _) hu w

/- English proof (translation)
The claim follows from `levi_add_fun hP _ j hy (P.mem_U _) (potSmoothAt A Q hQ _ j ⟨hy, Q.mem_U _⟩) w`.
-/
theorem leviAt_add {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w :=
  levi_add_fun hP _ j hy (P.mem_U _) (potSmoothAt A Q hQ _ j ⟨hy, Q.mem_U _⟩) w

/- English proof (translation)
Establish `he : (P.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm = c • (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm)` using `rfl`. Unfold `leviAt`. Rewrite using `[he]`. Simplify using `only [levi, fderiv_const_smul_field, Pi.smul_apply]`. Simplify using `only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviAt_rsmul (P : LocPot X) (c : ℝ) (j : Fin A.n) (y w : Fin e → ℂ) :
    leviAt A (P.rsmul c) j y w = c * leviAt A P j y w := by
  have he : (P.rsmul c).φ ((A.chart j).symm y) ∘ (A.chart j).symm =
    c • (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) := rfl
  unfold leviAt
  rw [he]
  simp only [levi, fderiv_const_smul_field, Pi.smul_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
The claim follows from `hP _ j y ⟨hy, P.mem_U _⟩ w`.
-/
theorem leviAt_nonneg {P : LocPot X} (hP : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ leviAt A P j y w :=
  hP _ j y ⟨hy, P.mem_U _⟩ w

/- English proof (translation)
Introduce `x j y hy w`. Break down `eq_or_ne w 0 with rfl | h` into its components or cases. Rewrite using `[levi_zero]`. Conclude with `(hP x j y hy w h).le`.
-/
theorem isPsh_of_isPosPot {P : LocPot X} (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  rcases eq_or_ne w 0 with rfl | h
  · rw [levi_zero]
  · exact (hP x j y hy w h).le

/- English proof (translation)
Establish `: fderiv ℝ (fun z => f z - c) = fderiv ℝ f` using `funext fun z => fderiv_sub_const c`. Unfold `levi`. Rewrite using `[this]`.
-/
theorem levi_sub_const (f : (Fin e → ℂ) → ℝ) (c : ℝ) (y w : Fin e → ℂ) :
    levi (fun z => f z - c) y w = levi f y w := by
  have : fderiv ℝ (fun z => f z - c) = fderiv ℝ f := funext fun z => fderiv_sub_const c
  unfold levi
  rw [this]

/- English proof (translation)
Establish `hp : ∀ i, (hessC (f i) y).PosSemidef` using `fun i => hessC_posSemidef_of_levi _ y (hf i) (h0 i)`. Use `⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hp, ?_⟩` and prove the remaining obligations. Unfold `maDens`. Use `mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hp fun i => ?_) (by positivity)` and prove the remaining obligations. Establish `h1 : ContDiffAt ℝ 2 (fun z => (-1 : ℝ) * f i z) y` using `contDiffAt_const.mul (hf i)`.

Establish `h2` using `hessC_posSemidef_of_levi (fun z => g i z + (-1 : ℝ) * f i z) y ((hg i).add h1) fun w => by`. Rewrite using `[levi_add_smul (-1) (hg i) (hf i)]`. Combine the linear relations using `[hle i w]`. Rewrite `h2` using `[hessC_add' _ _ y (hg i) h1, hessC_const_mul']`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `[sub_eq_add_neg]`.
-/
theorem maDens_mono_pt (f g : Fin e → (Fin e → ℂ) → ℝ) (y : Fin e → ℂ)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) y) (hg : ∀ i, ContDiffAt ℝ 2 (g i) y)
    (h0 : ∀ i w, 0 ≤ levi (f i) y w) (hle : ∀ i w, levi (f i) y w ≤ levi (g i) y w) :
    0 ≤ maDens f y ∧ maDens f y ≤ maDens g y := by
  have hp : ∀ i, (hessC (f i) y).PosSemidef := fun i => hessC_posSemidef_of_levi _ y (hf i) (h0 i)
  refine ⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hp, ?_⟩
  unfold maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hp fun i => ?_) (by positivity)
  have h1 : ContDiffAt ℝ 2 (fun z => (-1 : ℝ) * f i z) y := contDiffAt_const.mul (hf i)
  have h2 := hessC_posSemidef_of_levi (fun z => g i z + (-1 : ℝ) * f i z) y ((hg i).add h1) fun w => by
    rw [levi_add_smul (-1) (hg i) (hf i)]
    linarith [hle i w]
  rw [hessC_add' _ _ y (hg i) h1, hessC_const_mul'] at h2
  convert h2 using 1
  simp [sub_eq_add_neg]

/- English proof (translation)
Introduce `y hy`. Assume the negation of the conclusion as `hneg`. Establish `ho : IsOpen (V ∩ f ⁻¹' Set.Iio 0)` using `hf.isOpen_inter_preimage hV isOpen_Iio`. Establish `hs : V ∩ f ⁻¹' Set.Iio 0 ⊆ N` using `fun z hz => by`. Assume the negation of the conclusion as `hz'`.

Conclude with `absurd (h z hz.1 hz') (not_le.2 hz.2)`. Use `ho.eq_empty_of_measure_zero (measure_mono_null hs hN)` as an intermediate fact. Conclude with `(this ▸ (⟨hy, not_le.1 hneg⟩ : y ∈ V ∩ f ⁻¹' Set.Iio 0) : y ∈ (∅ : Set _))`.
-/
theorem nonneg_of_null {V N : Set (Fin e → ℂ)} (hV : IsOpen V) (hN : volume N = 0)
    {f : (Fin e → ℂ) → ℝ} (hf : ContinuousOn f V) (h : ∀ y ∈ V, y ∉ N → 0 ≤ f y) :
    ∀ y ∈ V, 0 ≤ f y := by
  intro y hy
  by_contra hneg
  have ho : IsOpen (V ∩ f ⁻¹' Set.Iio 0) := hf.isOpen_inter_preimage hV isOpen_Iio
  have hs : V ∩ f ⁻¹' Set.Iio 0 ⊆ N := fun z hz => by
    by_contra hz'
    exact absurd (h z hz.1 hz') (not_le.2 hz.2)
  have := ho.eq_empty_of_measure_zero (measure_mono_null hs hN)
  exact (this ▸ (⟨hy, not_le.1 hneg⟩ : y ∈ V ∩ f ⁻¹' Set.Iio 0) : y ∈ (∅ : Set _))

section Meas

variable [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Establish `hTm` using `(A.chart j).open_target.measurableSet`. Establish `hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target)` using `(A.chart j).continuousOn_symm.aemeasurable hTm`. Establish `hn` using `hsm.nullMeasurableSet_preimage hE`. Use `⟨hn, ?_⟩` and prove the remaining obligations. Unfold `chartMeasure`.

Rewrite using `[Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hE, withDensity_apply₀ _ hn]`.
-/
theorem chartMeasure_apply (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) {E : Set X}
    (hE : MeasurableSet E) :
    NullMeasurableSet ((A.chart j).symm ⁻¹' E) (volume.restrict (A.chart j).target) ∧
    chartMeasure A P Φ j E = ∫⁻ y in (A.chart j).symm ⁻¹' E,
      ENNReal.ofReal (P.χ j ((A.chart j).symm y) * locDens A Φ j y)
        ∂(volume.restrict (A.chart j).target) := by
  have hTm := (A.chart j).open_target.measurableSet
  have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hTm
  have hn := hsm.nullMeasurableSet_preimage hE
  refine ⟨hn, ?_⟩
  unfold chartMeasure
  rw [Measure.map_apply_of_aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)) hE,
    withDensity_apply₀ _ hn]

/- English proof (translation)
Distinguish the cases in `hne : Nonempty (ChartPartition A)`. Rewrite using `[maMeasure_eq_sum A Φ hne, maMeasure_eq_sum A _ hne]`. Simplify using `only [Measure.coe_finsetSum, Finset.sum_apply]`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Take `⟨hn, h1⟩` from `chartMeasure_apply hne.some Φ j hE`.

Rewrite using `[h1, (chartMeasure_apply hne.some Ψ j hE).2]`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem₀ hn, ae_restrict_of_ae (ae_restrict_mem (A.chart j).open_target.measurableSet)] with y h1 h2`. Conclude with `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (h j y h2 h1) (hne.some.nonneg j _))`. Unfold `maMeasure`.

Rewrite using `[dif_neg hne, dif_neg hne]`.
-/
theorem maMeasure_mono_on (Φ Ψ : Fin e → LocPot X) {E : Set X} (hE : MeasurableSet E)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ E → locDens A Φ j y ≤ locDens A Ψ j y) :
    maMeasure A Φ E ≤ maMeasure A Ψ E := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne, maMeasure_eq_sum A _ hne]
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨hn, h1⟩ := chartMeasure_apply hne.some Φ j hE
    rw [h1, (chartMeasure_apply hne.some Ψ j hE).2]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem₀ hn,
      ae_restrict_of_ae (ae_restrict_mem (A.chart j).open_target.measurableSet)] with y h1 h2
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (h j y h2 h1) (hne.some.nonneg j _))
  · unfold maMeasure
    rw [dif_neg hne, dif_neg hne]

/- English proof (translation)
Distinguish the cases in `hne : Nonempty (ChartPartition A)`. Rewrite using `[maMeasure_eq_sum A Φ hne]`. Simplify using `only [Measure.coe_finsetSum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[(chartMeasure_apply hne.some Φ j hZ).2]`.

Apply `setLIntegral_measure_zero` to reduce the goal to its premises. Rewrite using `[Measure.restrict_apply' (A.chart j).open_target.measurableSet, Set.inter_comm]`. Conclude with `h j`. Unfold `maMeasure`. Rewrite using `[dif_neg hne]`.

Both sides reduce to the same expression.
-/
theorem maMeasure_null (Φ : Fin e → LocPot X) {Z : Set X} (hZ : MeasurableSet Z)
    (h : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0) : maMeasure A Φ Z = 0 := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne]
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [(chartMeasure_apply hne.some Φ j hZ).2]
    apply setLIntegral_measure_zero
    rw [Measure.restrict_apply' (A.chart j).open_target.measurableSet, Set.inter_comm]
    exact h j
  · unfold maMeasure
    rw [dif_neg hne]
    rfl

end Meas

end GlobalTheory.ShellMass

namespace GlobalTheory.ShellMass

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

/- English proof (translation)
Break down `hc with hs | hb` into its components or cases. Establish `h0 : ∀ x, u x ≤ 0`. Introduce `x`. Take `⟨j, hj⟩` from `A.cover x`. Use `nonneg_of_null (A.chart j).open_target (hZ0 j) (f := fun y => -(u ∘ (A.chart j).symm) y) (fun y hy => (smoothOn_contDiffAt isOpen_univ hs j hy trivial).continuousAt.neg.continuousWithinAt) (fun y hy hn => neg_nonneg.2 (hu0 _ fun h => hn ⟨hy, h⟩)) _ ((A.chart j).map_source hj)` as an intermediate fact.

Simplify `this` using `[(A.chart j).left_inv hj]`. Take `⟨v, η, h1, h2, h3, h4, h5, h6, h7⟩` from `GlobalTheory.T.psh_extension_off_closed_set e X A Om ∅ u M hM isClosed_empty hO hOp (by rw [Set.compl_empty]; exact hs) (fun x _ => h0 x) (by`. Introduce `x j y hy w`. Establish `hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x)` using `(A.chart j).isOpen_inter_preimage_symm (Om.isOpen_U x)`. Establish `hcd : ContDiffOn ℝ 2 ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x)` using `fun y hy => ((potSmoothAt A Om hO x j hy).add (smoothOn_contDiffAt isOpen_univ hs j hy.1 trivial)).contDiffWithinAt`.

Use `nonneg_of_null hV (hZ0 j) (f := fun y => levi ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) y w) ?_ ?_ y ⟨hy.1, hy.2.1⟩` and prove the remaining obligations. Conclude with `(continuousOn_levi hV hcd).comp (f := fun y => (y, w)) (by fun_prop) fun y hy => ⟨hy, trivial⟩`. Introduce `y hy hn`. Rewrite using `[levi_add_fun hO x j hy.1 hy.2 (smoothOn_contDiffAt isOpen_univ hs j hy.1 trivial)]`. Conclude with `hp j y hy.1 (fun h => hn ⟨hy.1, h⟩) w) (fun a => by simp)`.

Conclude with `⟨v, η, h1, h2, h3, h4, h5, fun x _ => h6 x (by simp), fun x _ => h7 x (by simp)⟩`. Conclude with `GlobalTheory.T.psh_extension_off_closed_set e X A Om Z u M hM hZ hO hOp hu hu0 (by`. Introduce `x j y hy w`. Rewrite using `[levi_add_fun hO x j hy.1 hy.2.1 (smoothOn_contDiffAt hZ.isOpen_compl hu j hy.1 hy.2.2)]`. Conclude with `hp j y hy.1 hy.2.2 w) hb`.
-/
theorem trunc [CompactSpace X] [T2Space X] {Om : LocPot X} {Z : Set X} {u : X → ℝ} {M : ℝ} (hM : 2 ≤ M)
    (hZ : IsClosed Z) (hZ0 : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) = 0)
    (hO : IsPotential A Om) (hOp : IsPsh A Om) (hu : A.SmoothOn Zᶜ u) (hu0 : ∀ x, x ∉ Z → u x ≤ 0)
    (hp : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w,
      0 ≤ leviAt A Om j y w + levi (u ∘ (A.chart j).symm) y w)
    (hc : A.Smooth u ∨ ToBot Z u) :
    ∃ (v : X → ℝ) (η : ℝ), A.Smooth v ∧ IsPsh A (Om + LocPot.ofFun v) ∧ (∀ x, -M ≤ v x ∧ v x ≤ 0) ∧
      0 ≤ η ∧ η ≤ 1 / 4 ∧ (∀ x, x ∉ Z → -M + 2 ≤ u x → v x = u x - η) ∧ ∀ x, x ∉ Z → u x - η ≤ v x := by
  rcases hc with hs | hb
  · have h0 : ∀ x, u x ≤ 0 := by
      intro x
      obtain ⟨j, hj⟩ := A.cover x
      have := nonneg_of_null (A.chart j).open_target (hZ0 j) (f := fun y => -(u ∘ (A.chart j).symm) y)
        (fun y hy => (smoothOn_contDiffAt isOpen_univ hs j hy trivial).continuousAt.neg.continuousWithinAt)
        (fun y hy hn => neg_nonneg.2 (hu0 _ fun h => hn ⟨hy, h⟩)) _ ((A.chart j).map_source hj)
      simpa [(A.chart j).left_inv hj] using this
    obtain ⟨v, η, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.psh_extension_off_closed_set e X A Om ∅ u M hM isClosed_empty hO hOp
      (by rw [Set.compl_empty]; exact hs) (fun x _ => h0 x) (by
        intro x j y hy w
        have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x) :=
          (A.chart j).isOpen_inter_preimage_symm (Om.isOpen_U x)
        have hcd : ContDiffOn ℝ 2 ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm)
            ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Om.U x) := fun y hy =>
          ((potSmoothAt A Om hO x j hy).add
            (smoothOn_contDiffAt isOpen_univ hs j hy.1 trivial)).contDiffWithinAt
        refine nonneg_of_null hV (hZ0 j)
          (f := fun y => levi ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) y w) ?_ ?_ y ⟨hy.1, hy.2.1⟩
        · exact (continuousOn_levi hV hcd).comp (f := fun y => (y, w)) (by fun_prop)
            fun y hy => ⟨hy, trivial⟩
        · intro y hy hn
          rw [levi_add_fun hO x j hy.1 hy.2 (smoothOn_contDiffAt isOpen_univ hs j hy.1 trivial)]
          exact hp j y hy.1 (fun h => hn ⟨hy.1, h⟩) w) (fun a => by simp)
    exact ⟨v, η, h1, h2, h3, h4, h5, fun x _ => h6 x (by simp), fun x _ => h7 x (by simp)⟩
  · exact GlobalTheory.T.psh_extension_off_closed_set e X A Om Z u M hM hZ hO hOp hu hu0 (by
      intro x j y hy w
      rw [levi_add_fun hO x j hy.1 hy.2.1 (smoothOn_contDiffAt hZ.isOpen_compl hu j hy.1 hy.2.2)]
      exact hp j y hy.1 hy.2.2 w) hb

/- English proof (translation)
The claim follows from `(smoothOn_continuousOn hZ.isOpen_compl hr).isOpen_inter_preimage hZ.isOpen_compl isOpen_Iio`.
-/
theorem isOpen_sub {Z : Set X} (hZ : IsClosed Z) {r : X → ℝ} (hr : A.SmoothOn Zᶜ r) (a : ℝ) :
    IsOpen {x | x ∉ Z ∧ r x < a} :=
  (smoothOn_continuousOn hZ.isOpen_compl hr).isOpen_inter_preimage hZ.isOpen_compl isOpen_Iio

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff]`. Use `⟨fun ⟨_, h⟩ => h.1, fun h => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_nat_gt (r x - a)`. Conclude with `⟨n, h, by linarith⟩`.
-/
theorem iUnion_sub (Z : Set X) (r : X → ℝ) (a : ℝ) : ⋃ n : ℕ, {x | x ∉ Z ∧ r x < a + n} = Zᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff]
  refine ⟨fun ⟨_, h⟩ => h.1, fun h => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (r x - a)
  exact ⟨n, h, by linarith⟩

/- English proof (translation)
Introduce `n m h x hx` and use `⟨hx.1, hx.2.trans_le (by have : (n : ℝ) ≤ m := Nat.cast_le.2 h; linarith)⟩`.
-/
theorem monotone_sub (Z : Set X) (r : X → ℝ) (a : ℝ) :
    Monotone fun n : ℕ => {x | x ∉ Z ∧ r x < a + n} := fun n m h x hx =>
  ⟨hx.1, hx.2.trans_le (by have : (n : ℝ) ≤ m := Nat.cast_le.2 h; linarith)⟩

/- English proof (translation)
Unfold `locDens maDens`. Rewrite using `[ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.mdisc_const]`. Use `hessC_const_mul' K (fun y' => Om.φ ((A.chart j).symm y) ((A.chart j).symm y')) y` as an intermediate fact. Establish `h2 : hessC (fun y' => (Om.rsmul K).φ ((A.chart j).symm y) ((A.chart j).symm y')) y = _` using `this`. Rewrite using `[h2, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locDens_rsmul (Om : LocPot X) (K : ℝ) (j : Fin A.n) (y : Fin e → ℂ) :
    locDens A (fun _ => Om.rsmul K) j y = K ^ e * locDens A (fun _ => Om) j y := by
  unfold locDens maDens
  rw [ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.mdisc_const]
  have := hessC_const_mul' K (fun y' => Om.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  have h2 : hessC (fun y' => (Om.rsmul K).φ ((A.chart j).symm y) ((A.chart j).symm y')) y = _ := this
  rw [h2, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Take `⟨hf, h⟩` from `maMeasure_thm A Φ hΦ hp`. Rewrite using `[(h _ measurable_const).2 (mIntegrableCont A Φ hΦ _ continuous_const)]`. Simplify using `[Measure.real]`.
-/
theorem mass_univ (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hp : ∀ i, IsPsh A (Φ i)) :
    maMeasure A Φ Set.univ = ENNReal.ofReal (mInt A Φ fun _ => 1) := by
  obtain ⟨hf, h⟩ := maMeasure_thm A Φ hΦ hp
  rw [(h _ measurable_const).2 (mIntegrableCont A Φ hΦ _ continuous_const)]
  simp [Measure.real]

/- English proof (translation)
Take `⟨hZ, hZ0, hO, hOpos, hr, hre, hb, hri, c, hc, hps⟩` from `hB`. Establish `hOp` using `isPsh_of_isPosPot hOpos`. Establish `hO' : IsPotential A (Om.rsmul K)` using `isPotentialRsmul A K Om hO`. Establish `hOp' : IsPsh A (Om.rsmul K)` using `isPshRsmul A K Om (by linarith) hO hOp`. Use `set Ω : Fin e → LocPot X := fun _ => Om.rsmul K with hΩ`.

Establish `hri' : MIntegrable A Ω (cut Z Set.univ r)` using `fun j S hS hSc => by`. Establish `: IntegrableOn (fun y => K ^ e * (cut Z Set.univ r ((A.chart j).symm y) * locDens A (fun _ => Om) j y)) S` using `Integrable.const_mul (hri j S hS hSc) _`. Use `this.congr_fun (fun y _ => ?_) hSc.measurableSet` and prove the remaining obligations. Simplify using `only [hΩ, locDens_rsmul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcm : Measurable (cut Z Set.univ r)`. Unfold `cut`. Rewrite using `[Set.univ_inter, ← Set.piecewise_eq_indicator]`. Conclude with `(smoothOn_continuousOn hZ.isOpen_compl hr).measurable_piecewise continuousOn_const hZ.isOpen_compl.measurableSet`. Take `⟨hΩf, hΩi⟩` from `maMeasure_thm A Ω (fun _ => hO') (fun _ => hOp')`.

Establish `hci : Integrable (cut Z Set.univ r) (maMeasure A Ω)` using `(hΩi _ hcm).1.1 hri'`. Use `set V := mInt A Ω fun _ => 1 with hV`. Establish `hV0 : 0 ≤ V` using `mIntNonneg A Ω (fun _ => hO') (fun _ => hOp') _ fun _ => zero_le_one`. Use `set J := ∫ x, (c * cut Z Set.univ r x + 1 / 4) ∂maMeasure A Ω with hJ`. Establish `hJ0 : 0 ≤ J` using `integral_nonneg fun x => by`.

Establish `: 0 ≤ cut Z Set.univ r x` using `Set.indicator_nonneg (fun x hx => (Real.exp_pos 1).le.trans (hre x hx.2)) x`. Check the signs of the components of the expression. Use `⟨(J + e * V) / c, by positivity, fun v M R hM hR hv => ?_⟩` and prove the remaining obligations. Use `set Ψ : Fin e → LocPot X := fun i => Om.rsmul K + LocPot.ofFun (v i) with hΨ`. Establish `hΨ1 : ∀ i, IsPotential A (Ψ i)` using `fun i => isPotentialAdd A _ _ hO' (isPotential_ofFun A _ (hv i).1)`.

Take `⟨hΨf, hΨi⟩` from `maMeasure_thm A Ψ hΨ1 fun i => (hv i).2.2`. Establish `key : ∀ n : ℕ, maMeasure A Ψ ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) ≤ ENNReal.ofReal ((J + e * V) / c * M ^ e / R)`. Introduce `n`. Establish `hcr : A.SmoothOn Zᶜ fun x => -c * r x` using `(smoothOnAlg A Zᶜ Zᶜ r r (-c) hr hr le_rfl).2`. Take `⟨w, η, h1, h2, h3, h4, h5, h6, h7⟩` from `trunc (M := c * (R + n) + 2) (u := fun x => -c * r x) (by have : 0 ≤ c * (R + n) := by positivity linarith) hZ hZ0 hO' hOp' hcr (fun x hx => by have := (Real.exp_pos 1).trans_le (hre x hx); nlinarith) (fun j y hy hn w => by`.

Establish `a1` using `hps j y hy hn w`. Rewrite `a1` using `[leviAt_add_ofFun hO j hy (smoothOn_contDiffAt hZ.isOpen_compl hcr j hy hn)]`. Rewrite using `[leviAt_rsmul]`. Establish `a2` using `leviAt_nonneg hOp j hy w`. Use the proof step `nlinarith)`.

Use the proof step `(Or.inr fun a => by`. Use `subset_trans (closure_mono fun x hx => ?_) (hb (a / c))` and prove the remaining obligations. Use `⟨hx.1, ?_⟩` and prove the remaining obligations. Use `hx.2` as an intermediate fact. Simplify using `only at this ⊢`.

Rewrite using `[neg_le_neg_iff, le_div_iff₀ hc]`. Use the proof step `linarith)`. Establish `hwc : Continuous fun x => -w x` using `(continuousOn_univ.1 (smoothOn_continuousOn isOpen_univ h1)).neg`. Establish `hcl` using `GlobalTheory.T.mixed_integral_bound_scaled_potentials e X A (Om.rsmul K) w v M hM hO' hOp' h1 (fun x => (h3 x).2) h2 hv`. Establish `hi1` using `mIntegrableCont A Ψ hΨ1 _ hwc`.

Establish `hi2` using `mIntegrableCont A Ω (fun _ => hO') _ hwc`. Establish `b1 : mInt A Ω (fun x => -w x) ≤ J`. Rewrite using `[(hΩi _ hwc.measurable).2 hi2]`. Use `integral_mono_ae ((hΩi _ hwc.measurable).1.1 hi2) ((hci.const_mul c).add (integrable_const _)) ?_` and prove the remaining obligations. Establish `hz : ∀ᵐ x ∂maMeasure A Ω, x ∉ Z` using `measure_eq_zero_iff_ae_notMem.1 (maMeasure_null Ω hZ.measurableSet hZ0)`.

Use `filter_upwards [hz] with x hx`. Establish `: cut Z Set.univ r x = r x` using `Set.indicator_of_mem (show x ∈ Set.univ ∩ Zᶜ from ⟨trivial, hx⟩) _`. Rewrite using `[this]`. Combine the linear relations using `[h7 x hx]`. Establish `b2 : c * R * (maMeasure A Ψ).real ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) ≤ mInt A Ψ (fun x => -w x)`.

Rewrite using `[(hΨi _ hwc.measurable).2 hi1]`. Use `le_trans ?_ (mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => neg_nonneg.2 (h3 x).2) ((hΨi _ hwc.measurable).1.1 hi1) (c * R))` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (measureReal_mono fun x hx => ?_) (by positivity)` and prove the remaining obligations. Establish `hx1 : R ≤ r x` using `not_lt.1 fun h => hx.2 ⟨hx.1.1, h⟩`. Establish `hx2 : r x < R + n` using `hx.1.2`.

Use `h6 x hx.1.1 (by nlinarith)` as an intermediate fact. Use `show c * R ≤ -w x`. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← ENNReal.ofReal_toReal (measure_ne_top (maMeasure A Ψ) _)]`.

Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hR, div_mul_eq_mul_div, le_div_iff₀ hc]`. Establish `hMe : 0 ≤ M ^ e` using `by positivity`. Establish `b3 : M ^ e * (mInt A Ω (fun x => -w x) + e * V) ≤ M ^ e * (J + e * V)` using `by gcongr`. Establish `b4 : mInt A Ψ (fun x => -w x) ≤ M ^ e * (mInt A Ω (fun x => -w x) + e * V)` using `hcl`.

Rewrite `b2` using `[Measure.real]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsub : {x | x ∉ Z ∧ r x < R}ᶜ ⊆ Z ∪ ⋃ n : ℕ, ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R})`. Introduce `x hx`. Distinguish the cases in `hz : x ∈ Z`.

Conclude with `Or.inl hz`. Rewrite using `[← Set.iUnion_diff, iUnion_sub]`. Conclude with `Or.inr ⟨hz, hx⟩`. Use `(measure_mono hsub).trans ((measure_union_le _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[maMeasure_null Ψ hZ.measurableSet hZ0, zero_add, Monotone.measure_iUnion fun n m h => Set.diff_subset_diff_left (monotone_sub Z r R h)]`.

Conclude with `iSup_le key`.
-/
theorem cheb {Z : Set X} {r : X → ℝ} {Om : LocPot X} (hB : IsBd A Z r Om) {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin e → X → ℝ) (M R : ℝ), 1 ≤ M → 0 < R →
      (∀ i, A.Smooth (v i) ∧ (∀ x, -M ≤ v i x ∧ v i x ≤ 0) ∧ IsPsh A (Om.rsmul K + LocPot.ofFun (v i))) →
      maMeasure A (fun i => Om.rsmul K + LocPot.ofFun (v i)) {x | x ∉ Z ∧ r x < R}ᶜ ≤
        ENNReal.ofReal (C * M ^ e / R) := by
  obtain ⟨hZ, hZ0, hO, hOpos, hr, hre, hb, hri, c, hc, hps⟩ := hB
  have hOp := isPsh_of_isPosPot hOpos
  have hO' : IsPotential A (Om.rsmul K) := isPotentialRsmul A K Om hO
  have hOp' : IsPsh A (Om.rsmul K) := isPshRsmul A K Om (by linarith) hO hOp
  set Ω : Fin e → LocPot X := fun _ => Om.rsmul K with hΩ
  have hri' : MIntegrable A Ω (cut Z Set.univ r) := fun j S hS hSc => by
    have : IntegrableOn (fun y => K ^ e * (cut Z Set.univ r ((A.chart j).symm y) *
      locDens A (fun _ => Om) j y)) S := Integrable.const_mul (hri j S hS hSc) _
    refine this.congr_fun (fun y _ => ?_) hSc.measurableSet
    simp only [hΩ, locDens_rsmul]
    ring
  have hcm : Measurable (cut Z Set.univ r) := by
    unfold cut
    rw [Set.univ_inter, ← Set.piecewise_eq_indicator]
    exact (smoothOn_continuousOn hZ.isOpen_compl hr).measurable_piecewise continuousOn_const
      hZ.isOpen_compl.measurableSet
  obtain ⟨hΩf, hΩi⟩ := maMeasure_thm A Ω (fun _ => hO') (fun _ => hOp')
  have hci : Integrable (cut Z Set.univ r) (maMeasure A Ω) := (hΩi _ hcm).1.1 hri'
  set V := mInt A Ω fun _ => 1 with hV
  have hV0 : 0 ≤ V := mIntNonneg A Ω (fun _ => hO') (fun _ => hOp') _ fun _ => zero_le_one
  set J := ∫ x, (c * cut Z Set.univ r x + 1 / 4) ∂maMeasure A Ω with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun x => by
    have : 0 ≤ cut Z Set.univ r x := Set.indicator_nonneg
      (fun x hx => (Real.exp_pos 1).le.trans (hre x hx.2)) x
    positivity
  refine ⟨(J + e * V) / c, by positivity, fun v M R hM hR hv => ?_⟩
  set Ψ : Fin e → LocPot X := fun i => Om.rsmul K + LocPot.ofFun (v i) with hΨ
  have hΨ1 : ∀ i, IsPotential A (Ψ i) := fun i =>
    isPotentialAdd A _ _ hO' (isPotential_ofFun A _ (hv i).1)
  obtain ⟨hΨf, hΨi⟩ := maMeasure_thm A Ψ hΨ1 fun i => (hv i).2.2
  have key : ∀ n : ℕ, maMeasure A Ψ ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) ≤
      ENNReal.ofReal ((J + e * V) / c * M ^ e / R) := by
    intro n
    have hcr : A.SmoothOn Zᶜ fun x => -c * r x := (smoothOnAlg A Zᶜ Zᶜ r r (-c) hr hr le_rfl).2
    obtain ⟨w, η, h1, h2, h3, h4, h5, h6, h7⟩ := trunc (M := c * (R + n) + 2) (u := fun x => -c * r x)
      (by have : 0 ≤ c * (R + n) := by positivity
          linarith) hZ hZ0 hO' hOp' hcr
      (fun x hx => by have := (Real.exp_pos 1).trans_le (hre x hx); nlinarith)
      (fun j y hy hn w => by
        have a1 := hps j y hy hn w
        rw [leviAt_add_ofFun hO j hy (smoothOn_contDiffAt hZ.isOpen_compl hcr j hy hn)] at a1
        rw [leviAt_rsmul]
        have a2 := leviAt_nonneg hOp j hy w
        nlinarith)
      (Or.inr fun a => by
        refine subset_trans (closure_mono fun x hx => ?_) (hb (a / c))
        refine ⟨hx.1, ?_⟩
        have := hx.2
        simp only at this ⊢
        rw [neg_le_neg_iff, le_div_iff₀ hc]
        linarith)
    have hwc : Continuous fun x => -w x :=
      (continuousOn_univ.1 (smoothOn_continuousOn isOpen_univ h1)).neg
    have hcl := GlobalTheory.T.mixed_integral_bound_scaled_potentials e X A (Om.rsmul K) w v M hM hO' hOp' h1 (fun x => (h3 x).2) h2 hv
    have hi1 := mIntegrableCont A Ψ hΨ1 _ hwc
    have hi2 := mIntegrableCont A Ω (fun _ => hO') _ hwc
    have b1 : mInt A Ω (fun x => -w x) ≤ J := by
      rw [(hΩi _ hwc.measurable).2 hi2]
      refine integral_mono_ae ((hΩi _ hwc.measurable).1.1 hi2)
        ((hci.const_mul c).add (integrable_const _)) ?_
      have hz : ∀ᵐ x ∂maMeasure A Ω, x ∉ Z :=
        measure_eq_zero_iff_ae_notMem.1 (maMeasure_null Ω hZ.measurableSet hZ0)
      filter_upwards [hz] with x hx
      have : cut Z Set.univ r x = r x := Set.indicator_of_mem (show x ∈ Set.univ ∩ Zᶜ from ⟨trivial, hx⟩) _
      rw [this]
      linarith [h7 x hx]
    have b2 : c * R * (maMeasure A Ψ).real ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) ≤
        mInt A Ψ (fun x => -w x) := by
      rw [(hΨi _ hwc.measurable).2 hi1]
      refine le_trans ?_ (mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall fun x => neg_nonneg.2 (h3 x).2) ((hΨi _ hwc.measurable).1.1 hi1) (c * R))
      refine mul_le_mul_of_nonneg_left (measureReal_mono fun x hx => ?_) (by positivity)
      have hx1 : R ≤ r x := not_lt.1 fun h => hx.2 ⟨hx.1.1, h⟩
      have hx2 : r x < R + n := hx.1.2
      have := h6 x hx.1.1 (by nlinarith)
      show c * R ≤ -w x
      rw [this]
      nlinarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top (maMeasure A Ψ) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hR, div_mul_eq_mul_div, le_div_iff₀ hc]
    have hMe : 0 ≤ M ^ e := by positivity
    have b3 : M ^ e * (mInt A Ω (fun x => -w x) + e * V) ≤ M ^ e * (J + e * V) := by gcongr
    have b4 : mInt A Ψ (fun x => -w x) ≤ M ^ e * (mInt A Ω (fun x => -w x) + e * V) := hcl
    rw [Measure.real] at b2
    nlinarith
  have hsub : {x | x ∉ Z ∧ r x < R}ᶜ ⊆
      Z ∪ ⋃ n : ℕ, ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) := by
    intro x hx
    by_cases hz : x ∈ Z
    · exact Or.inl hz
    · rw [← Set.iUnion_diff, iUnion_sub]
      exact Or.inr ⟨hz, hx⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [maMeasure_null Ψ hZ.measurableSet hZ0, zero_add,
    Monotone.measure_iUnion fun n m h => Set.diff_subset_diff_left (monotone_sub Z r R h)]
  exact iSup_le key

end GlobalTheory.ShellMass

namespace GlobalTheory.ShellMass

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

/- English proof (translation)
Introduce `y0 hy0`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Establish `hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (θ i).U ((A.chart j).symm y0)) ∩ Zᶜ))` using `(A.chart j).isOpen_inter_preimage_symm ((isOpen_iInter_of_finite fun i => (θ i).isOpen_U _).inter hZ.isOpen_compl)`. Establish `hy0V : y0 ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ((⋂ i, (θ i).U ((A.chart j).symm y0)) ∩ Zᶜ)` using `⟨hy0.1, Set.mem_iInter.2 fun i => (θ i).mem_U _, hy0.2⟩`. Establish `hcd : ∀ i x, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ (θ i).U x → (A.chart j).symm y ∉ Z → ContDiffAt ℝ 2 ((fun z => (θ i).φ x z + u i z) ∘ (A.chart j).symm) y` using `fun i x y hy h1 h2 => (potSmoothAt A _ (hθ i) x j ⟨hy, h1⟩).add (smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy h2)`.

Establish `heq : maDens (fun i => (fun z => (θ i).φ ((A.chart j).symm y0) z + u i z) ∘ (A.chart j).symm) =ᶠ[nhds y0] locDens A (fun i => θ i + LocPot.ofFun (u i)) j` using `by filter_upwards [hVo.mem_nhds hy0V] with y hy`. Establish `m1 : ∀ i, (A.chart j).symm y ∈ (θ i).U ((A.chart j).symm y0)` using `fun i => Set.mem_iInter.1 hy.2.1 i`. Establish `hl : ∀ i w, levi ((fun z => (θ i).φ ((A.chart j).symm y0) z + u i z) ∘ (A.chart j).symm) y w = levi ((fun z => (θ i).φ ((A.chart j).symm y) z + u i z) ∘ (A.chart j).symm) y w` using `fun i w => by`. Use `smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy.1 hy.2.2` as an intermediate fact. Rewrite using `[levi_add_fun (hθ i) _ j hy.1 (m1 i) this, levi_add_fun (hθ i) _ j hy.1 ((θ i).mem_U _) this]`.

Establish `h0 : ∀ i w, 0 ≤ levi ((fun z => (θ i).φ ((A.chart j).symm y) z + u i z) ∘ (A.chart j).symm) y w` using `fun i w => hp i j y hy.1 hy.2.2 w`. Establish `c1` using `fun i => hcd i _ y hy.1 (m1 i) hy.2.2`. Establish `c2` using `fun i => hcd i _ y hy.1 ((θ i).mem_U _) hy.2.2`. Conclude with `le_antisymm (maDens_mono_pt _ _ y c1 c2 (fun i w => (hl i w).symm ▸ h0 i w) fun i w => (hl i w).le).2 (maDens_mono_pt _ _ y c2 c1 h0 fun i w => (hl i w).ge).2`. Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations.

Use `(maDens_continuousOn _ _ hVo fun i y hy => ?_).continuousAt (hVo.mem_nhds hy0V)` and prove the remaining obligations. Conclude with `(hcd i _ y hy.1 (Set.mem_iInter.1 hy.2.1 i) hy.2.2).contDiffWithinAt`.
-/
theorem locDens_contOn {Z : Set X} (hZ : IsClosed Z) {θ : Fin e → LocPot X} {u : Fin e → X → ℝ}
    (hθ : ∀ i, IsPotential A (θ i)) (hu : ∀ i, A.SmoothOn Zᶜ (u i))
    (hp : ∀ i, PshOff A Z (θ i + LocPot.ofFun (u i))) (j : Fin A.n) :
    ContinuousOn (locDens A (fun i => θ i + LocPot.ofFun (u i)) j)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) := by
  intro y0 hy0
  apply ContinuousAt.continuousWithinAt
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      ((⋂ i, (θ i).U ((A.chart j).symm y0)) ∩ Zᶜ)) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((isOpen_iInter_of_finite fun i => (θ i).isOpen_U _).inter hZ.isOpen_compl)
  have hy0V : y0 ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      ((⋂ i, (θ i).U ((A.chart j).symm y0)) ∩ Zᶜ) :=
    ⟨hy0.1, Set.mem_iInter.2 fun i => (θ i).mem_U _, hy0.2⟩
  have hcd : ∀ i x, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ (θ i).U x → (A.chart j).symm y ∉ Z →
      ContDiffAt ℝ 2 ((fun z => (θ i).φ x z + u i z) ∘ (A.chart j).symm) y := fun i x y hy h1 h2 =>
    (potSmoothAt A _ (hθ i) x j ⟨hy, h1⟩).add (smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy h2)
  have heq : maDens (fun i => (fun z => (θ i).φ ((A.chart j).symm y0) z + u i z) ∘ (A.chart j).symm)
      =ᶠ[nhds y0] locDens A (fun i => θ i + LocPot.ofFun (u i)) j := by
    filter_upwards [hVo.mem_nhds hy0V] with y hy
    have m1 : ∀ i, (A.chart j).symm y ∈ (θ i).U ((A.chart j).symm y0) := fun i => Set.mem_iInter.1 hy.2.1 i
    have hl : ∀ i w, levi ((fun z => (θ i).φ ((A.chart j).symm y0) z + u i z) ∘ (A.chart j).symm) y w =
        levi ((fun z => (θ i).φ ((A.chart j).symm y) z + u i z) ∘ (A.chart j).symm) y w := fun i w => by
      have := smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy.1 hy.2.2
      rw [levi_add_fun (hθ i) _ j hy.1 (m1 i) this, levi_add_fun (hθ i) _ j hy.1 ((θ i).mem_U _) this]
    have h0 : ∀ i w, 0 ≤ levi ((fun z => (θ i).φ ((A.chart j).symm y) z + u i z) ∘ (A.chart j).symm) y w :=
      fun i w => hp i j y hy.1 hy.2.2 w
    have c1 := fun i => hcd i _ y hy.1 (m1 i) hy.2.2
    have c2 := fun i => hcd i _ y hy.1 ((θ i).mem_U _) hy.2.2
    exact le_antisymm (maDens_mono_pt _ _ y c1 c2 (fun i w => (hl i w).symm ▸ h0 i w)
      fun i w => (hl i w).le).2 (maDens_mono_pt _ _ y c2 c1 h0 fun i w => (hl i w).ge).2
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i y hy => ?_).continuousAt (hVo.mem_nhds hy0V)
  exact (hcd i _ y hy.1 (Set.mem_iInter.1 hy.2.1 i) hy.2.2).contDiffWithinAt

variable [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Establish `hTm` using `(A.chart j).open_target.measurableSet`. Establish `hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target)` using `(A.chart j).continuousOn_symm.aemeasurable hTm`. Establish `hV` using `((A.chart j).isOpen_inter_preimage_symm hU).measurableSet`. Establish `h1 : Measurable (((A.chart j).target ∩ (A.chart j).symm ⁻¹' U).indicator (locDens A Φ j))`. Rewrite using `[← Set.piecewise_eq_indicator]`.

Conclude with `hc.measurable_piecewise continuousOn_const hV`. Establish `h2` using `(((measurable_const (a := (1 : ℝ))).indicator hE).comp_aemeasurable hsm).mul h1.aemeasurable`. Use `h2.congr (ae_restrict_of_forall_mem hTm fun y hy => ?_)` and prove the remaining obligations. Distinguish the cases in `h : (A.chart j).symm y ∈ E`. Simplify using `only [Pi.mul_apply, Function.comp_apply]`.

Rewrite using `[Set.indicator_of_mem (show y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U from ⟨hy, hEU h⟩)]`. Simplify using `[Set.indicator_of_notMem h]`.
-/
theorem aemeas_ind {Φ : Fin e → LocPot X} {U E : Set X} (hU : IsOpen U) (hE : MeasurableSet E)
    (hEU : E ⊆ U) (j : Fin A.n)
    (hc : ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    AEMeasurable (fun y => E.indicator (fun _ => (1 : ℝ)) ((A.chart j).symm y) * locDens A Φ j y)
      (volume.restrict (A.chart j).target) := by
  have hTm := (A.chart j).open_target.measurableSet
  have hsm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hTm
  have hV := ((A.chart j).isOpen_inter_preimage_symm hU).measurableSet
  have h1 : Measurable (((A.chart j).target ∩ (A.chart j).symm ⁻¹' U).indicator (locDens A Φ j)) := by
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const hV
  have h2 := (((measurable_const (a := (1 : ℝ))).indicator hE).comp_aemeasurable hsm).mul h1.aemeasurable
  refine h2.congr (ae_restrict_of_forall_mem hTm fun y hy => ?_)
  by_cases h : (A.chart j).symm y ∈ E
  · simp only [Pi.mul_apply, Function.comp_apply]
    rw [Set.indicator_of_mem (show y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U from ⟨hy, hEU h⟩)]
  · simp [Set.indicator_of_notMem h]

variable [CompactSpace X] [T2Space X]

/- English proof (translation)
Establish `hne : Nonempty (ChartPartition A)` using `existsPartition A`. Rewrite using `[mInt_eq_integralWith A Φ hne]`. Rewrite `hle` using `[maMeasure_eq_sum A Φ hne]`. Simplify using `only [Measure.coe_finsetSum, Finset.sum_apply] at hle`. Establish `hfin : ∀ j ∈ Finset.univ, chartMeasure A hne.some Φ j E ≠ ⊤` using `fun j hj => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((Finset.single_le_sum (f := fun j => chartMeasure A hne.some Φ j E) (fun _ _ => by positivity) hj).trans hle)`.

Use `le_trans (le_of_eq ?_) (ENNReal.toReal_le_of_le_ofReal hC hle)` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_sum hfin]`. Unfold `integralWith`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hTm` using `(A.chart j).open_target.measurableSet`.

Take `⟨hn, h1⟩` from `chartMeasure_apply hne.some Φ j hE`. Rewrite using `[h1, integral_eq_lintegral_of_nonneg_ae, ← lintegral_indicator₀ hn]`. Use `congr 1`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Distinguish the cases in `h : (A.chart j).symm y ∈ E`.

Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem (show y ∈ (A.chart j).symm ⁻¹' E from h), mul_one]`. Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (show y ∉ (A.chart j).symm ⁻¹' E from h)]`. Simplify using the standard rewrite rules. Use `ae_restrict_of_forall_mem hTm fun y hy => ?_` and prove the remaining obligations. Distinguish the cases in `h : (A.chart j).symm y ∈ E`.

Simplify using `only [Set.indicator_of_mem h, mul_one, Pi.zero_apply]`. Conclude with `mul_nonneg (hne.some.nonneg j _) (h0 j y hy (hEU h))`. Simplify using `[Set.indicator_of_notMem h]`. Simplify using `only [mul_assoc]`. Conclude with `(((chi_comp_continuousOn hne.some j).aemeasurable hTm).mul (aemeas_ind hU hE hEU j (hc j))).aestronglyMeasurable`.
-/
theorem mInt_ind_le {Φ : Fin e → LocPot X} {U E : Set X} (hU : IsOpen U) (hE : MeasurableSet E)
    (hEU : E ⊆ U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (h0 : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ U → 0 ≤ locDens A Φ j y)
    {C : ℝ} (hC : 0 ≤ C) (hle : maMeasure A Φ E ≤ ENNReal.ofReal C) :
    mInt A Φ (E.indicator fun _ => 1) ≤ C := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  rw [mInt_eq_integralWith A Φ hne]
  rw [maMeasure_eq_sum A Φ hne] at hle
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at hle
  have hfin : ∀ j ∈ Finset.univ, chartMeasure A hne.some Φ j E ≠ ⊤ := fun j hj =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((Finset.single_le_sum (f := fun j => chartMeasure A hne.some Φ j E) (fun _ _ => by positivity) hj).trans hle)
  refine le_trans (le_of_eq ?_) (ENNReal.toReal_le_of_le_ofReal hC hle)
  rw [ENNReal.toReal_sum hfin]
  unfold integralWith
  refine Finset.sum_congr rfl fun j _ => ?_
  have hTm := (A.chart j).open_target.measurableSet
  obtain ⟨hn, h1⟩ := chartMeasure_apply hne.some Φ j hE
  rw [h1, integral_eq_lintegral_of_nonneg_ae, ← lintegral_indicator₀ hn]
  · congr 1
    refine lintegral_congr fun y => ?_
    by_cases h : (A.chart j).symm y ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show y ∈ (A.chart j).symm ⁻¹' E from h), mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show y ∉ (A.chart j).symm ⁻¹' E from h)]
      simp
  · refine ae_restrict_of_forall_mem hTm fun y hy => ?_
    by_cases h : (A.chart j).symm y ∈ E
    · simp only [Set.indicator_of_mem h, mul_one, Pi.zero_apply]
      exact mul_nonneg (hne.some.nonneg j _) (h0 j y hy (hEU h))
    · simp [Set.indicator_of_notMem h]
  · simp only [mul_assoc]
    exact (((chi_comp_continuousOn hne.some j).aemeasurable hTm).mul
      (aemeas_ind hU hE hEU j (hc j))).aestronglyMeasurable

/- English proof (translation)
Establish `hne : Nonempty (ChartPartition A)` using `existsPartition A`. Establish `hTm` using `(A.chart j).open_target.measurableSet`. Establish `hI : IsCompact ((A.chart j).symm '' S)` using `hSc.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hS)`. Establish `hIs : (A.chart j).symm '' S ⊆ (A.chart j).source` using `Set.image_subset_iff.mpr fun y hy => (A.chart j).map_target (hS hy)`. Take `⟨hf, hi⟩` from `maMeasure_thm A Φ hΦ hp`.

Use `set g : X → ℝ := ((A.chart j).symm '' S).indicator fun _ => 1 with hg`. Establish `hgm : Measurable g` using `measurable_const.indicator hI.measurableSet`. Establish `hgi : Integrable g (maMeasure A Φ)` using `(integrable_const _).indicator hI.measurableSet`. Establish `hgM` using `(hi g hgm).1.2 hgi`. Establish `hts : tsupport g ⊆ (A.chart j).source` using `(closure_minimal Set.support_indicator_subset hI.isClosed).trans hIs`.

Establish `h1 : mInt A Φ g ≤ mInt A Φ fun _ => 1`. Rewrite using `[(hi g hgm).2 hgM, (hi _ measurable_const).2 (mIntegrableCont A Φ hΦ _ continuous_const)]`. Conclude with `integral_mono hgi (integrable_const _) fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x`. Establish `h2 : mInt A Φ g = ∫ y in S, locDens A Φ j y`. Rewrite using `[mInt_eq_integralWith A Φ hne, mIntLocalize A hne.some Φ hΦ j g hts hgM, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hS]`.

Use `setIntegral_congr_fun hSc.measurableSet fun y hy => ?_` and prove the remaining obligations. Simplify using `only [hg]`. Rewrite using `[Set.indicator_of_mem (Set.mem_image_of_mem _ hy), one_mul]`. Introduce and unpack `y ⟨hy, hyS⟩`. Establish `: (A.chart j).symm y ∉ (A.chart j).symm '' S`.

Introduce and unpack `⟨z, hz, h⟩`. Conclude with `hyS ((A.chart j).symm.injOn (hS hz) hy h ▸ hz)`. Simplify using `only [hg]`. Rewrite using `[Set.indicator_of_notMem this, zero_mul]`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (((locDensCont A Φ hΦ j).mono hS).integrableOn_compact hSc) (ae_restrict_of_forall_mem hSc.measurableSet fun y hy => locDens_nonneg_of_psh A Φ hΦ hp j (hS hy))]`.

Conclude with `ENNReal.ofReal_le_ofReal (h2 ▸ h1)`.
-/
theorem chart_le_mass (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hp : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {S : Set (Fin e → ℂ)} (hS : S ⊆ (A.chart j).target) (hSc : IsCompact S) :
    ∫⁻ y in S, ENNReal.ofReal (locDens A Φ j y) ≤ ENNReal.ofReal (mInt A Φ fun _ => 1) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hTm := (A.chart j).open_target.measurableSet
  have hI : IsCompact ((A.chart j).symm '' S) :=
    hSc.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hS)
  have hIs : (A.chart j).symm '' S ⊆ (A.chart j).source :=
    Set.image_subset_iff.mpr fun y hy => (A.chart j).map_target (hS hy)
  obtain ⟨hf, hi⟩ := maMeasure_thm A Φ hΦ hp
  set g : X → ℝ := ((A.chart j).symm '' S).indicator fun _ => 1 with hg
  have hgm : Measurable g := measurable_const.indicator hI.measurableSet
  have hgi : Integrable g (maMeasure A Φ) := (integrable_const _).indicator hI.measurableSet
  have hgM := (hi g hgm).1.2 hgi
  have hts : tsupport g ⊆ (A.chart j).source :=
    (closure_minimal Set.support_indicator_subset hI.isClosed).trans hIs
  have h1 : mInt A Φ g ≤ mInt A Φ fun _ => 1 := by
    rw [(hi g hgm).2 hgM, (hi _ measurable_const).2 (mIntegrableCont A Φ hΦ _ continuous_const)]
    exact integral_mono hgi (integrable_const _) fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x
  have h2 : mInt A Φ g = ∫ y in S, locDens A Φ j y := by
    rw [mInt_eq_integralWith A Φ hne, mIntLocalize A hne.some Φ hΦ j g hts hgM,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hS]
    · refine setIntegral_congr_fun hSc.measurableSet fun y hy => ?_
      simp only [hg]
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), one_mul]
    · rintro y ⟨hy, hyS⟩
      have : (A.chart j).symm y ∉ (A.chart j).symm '' S := by
        rintro ⟨z, hz, h⟩
        exact hyS ((A.chart j).symm.injOn (hS hz) hy h ▸ hz)
      simp only [hg]
      rw [Set.indicator_of_notMem this, zero_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal (((locDensCont A Φ hΦ j).mono hS).integrableOn_compact hSc)
    (ae_restrict_of_forall_mem hSc.measurableSet fun y hy => locDens_nonneg_of_psh A Φ hΦ hp j (hS hy))]
  exact ENNReal.ofReal_le_ofReal (h2 ▸ h1)

/- English proof (translation)
Introduce `j S hS hSc`. Establish `hSm` using `hSc.measurableSet`. Use `⟨((aemeas_ind hU hU.measurableSet le_rfl j (hc j)).mono_measure (Measure.restrict_mono hS le_rfl)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `set W : ℕ → Set (Fin e → ℂ) := fun n => S ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O n) with hW`. Establish `hWm : ∀ n, MeasurableSet (W n)` using `fun n => hSm.inter ((A.chart j).isOpen_inter_preimage_symm (hO n)).measurableSet`.

Establish `hWmono : Monotone W` using `fun n m h y hy => ⟨hy.1, hy.2.1, hm h hy.2.2⟩`. Establish `h1 : ∫⁻ y in S, ‖U.indicator (fun _ => (1 : ℝ)) ((A.chart j).symm y) * locDens A Φ j y‖ₑ = ∫⁻ y in ⋃ n, W n, ENNReal.ofReal (locDens A Φ j y)`. Rewrite using `[← lintegral_indicator hSm, ← lintegral_indicator (MeasurableSet.iUnion hWm)]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ ⋃ n, W n`.

Take `⟨n, hn⟩` from `Set.mem_iUnion.1 hy`. Establish `hyU : (A.chart j).symm y ∈ U` using `hU' ▸ Set.mem_iUnion.2 ⟨n, hn.2.2⟩`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hn.1, Set.indicator_of_mem hyU, one_mul, Real.enorm_eq_ofReal (h0 j y hn.2.1 hyU)]`. Rewrite using `[Set.indicator_of_notMem hy]`. Distinguish the cases in `hyS : y ∈ S`.

Establish `hyU : (A.chart j).symm y ∉ U` using `fun h => by`. Rewrite `h` using `[← hU']`. Take `⟨n, hn⟩` from `Set.mem_iUnion.1 h`. Conclude with `hy (Set.mem_iUnion.2 ⟨n, hyS, hS hyS, hn⟩)`. Rewrite using `[Set.indicator_of_mem hyS, Set.indicator_of_notMem hyU]`.

Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hyS]`. Unfold `HasFiniteIntegral`. Rewrite using `[h1, setLIntegral_iUnion_of_directed _ hWmono.directed_le]`. Use `lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := C))` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mIntegrable_ind {Φ : Fin e → LocPot X} {U : Set X} (hU : IsOpen U)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    (h0 : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ U → 0 ≤ locDens A Φ j y)
    (O : ℕ → Set X) (hO : ∀ n, IsOpen (O n)) (hm : Monotone O) (hU' : ⋃ n, O n = U)
    (Ψ : ℕ → Fin e → LocPot X) (hΨ : ∀ n i, IsPotential A (Ψ n i)) (hp : ∀ n i, IsPsh A (Ψ n i))
    (hle : ∀ n j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ O n →
      locDens A Φ j y ≤ locDens A (Ψ n) j y) {C : ℝ} (hC : ∀ n, mInt A (Ψ n) (fun _ => 1) ≤ C) :
    MIntegrable A Φ (U.indicator fun _ => 1) := by
  intro j S hS hSc
  have hSm := hSc.measurableSet
  refine ⟨((aemeas_ind hU hU.measurableSet le_rfl j (hc j)).mono_measure
    (Measure.restrict_mono hS le_rfl)).aestronglyMeasurable, ?_⟩
  set W : ℕ → Set (Fin e → ℂ) := fun n => S ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O n) with hW
  have hWm : ∀ n, MeasurableSet (W n) := fun n =>
    hSm.inter ((A.chart j).isOpen_inter_preimage_symm (hO n)).measurableSet
  have hWmono : Monotone W := fun n m h y hy => ⟨hy.1, hy.2.1, hm h hy.2.2⟩
  have h1 : ∫⁻ y in S, ‖U.indicator (fun _ => (1 : ℝ)) ((A.chart j).symm y) * locDens A Φ j y‖ₑ =
      ∫⁻ y in ⋃ n, W n, ENNReal.ofReal (locDens A Φ j y) := by
    rw [← lintegral_indicator hSm, ← lintegral_indicator (MeasurableSet.iUnion hWm)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ ⋃ n, W n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      have hyU : (A.chart j).symm y ∈ U := hU' ▸ Set.mem_iUnion.2 ⟨n, hn.2.2⟩
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hn.1, Set.indicator_of_mem hyU, one_mul,
        Real.enorm_eq_ofReal (h0 j y hn.2.1 hyU)]
    · rw [Set.indicator_of_notMem hy]
      by_cases hyS : y ∈ S
      · have hyU : (A.chart j).symm y ∉ U := fun h => by
          rw [← hU'] at h
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
          exact hy (Set.mem_iUnion.2 ⟨n, hyS, hS hyS, hn⟩)
        rw [Set.indicator_of_mem hyS, Set.indicator_of_notMem hyU]
        simp
      · rw [Set.indicator_of_notMem hyS]
  unfold HasFiniteIntegral
  rw [h1, setLIntegral_iUnion_of_directed _ hWmono.directed_le]
  refine lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := C))
  calc ∫⁻ y in W n, ENNReal.ofReal (locDens A Φ j y)
      ≤ ∫⁻ y in W n, ENNReal.ofReal (locDens A (Ψ n) j y) :=
        setLIntegral_mono' (hWm n) fun y hy => ENNReal.ofReal_le_ofReal (hle n j y hy.2.1 hy.2.2)
    _ ≤ ∫⁻ y in S, ENNReal.ofReal (locDens A (Ψ n) j y) := lintegral_mono_set Set.inter_subset_left
    _ ≤ _ := (chart_le_mass _ (hΨ n) (hp n) j hS hSc).trans (ENNReal.ofReal_le_ofReal (hC n))

end GlobalTheory.ShellMass

namespace GlobalTheory.ShellMass

/- English proof (translation)
Introduce `e X _ _ _ A Z r Om hB K hK`. Use `borelize X`. Take `⟨C, hC0, hC⟩` from `cheb hB hK`. Take `⟨hZ, hZ0, hO, hOpos, hr, hre, hb, hri, -⟩` from `hB`. Establish `hOp` using `isPsh_of_isPosPot hOpos`.

Establish `hO' : IsPotential A (Om.rsmul K)` using `isPotentialRsmul A K Om hO`. Establish `hOp' : IsPsh A (Om.rsmul K)` using `isPshRsmul A K Om (by linarith) hO hOp`. Use `set V := mInt A (fun _ => Om.rsmul K) fun _ => 1 with hV`. Establish `hV0 : 0 ≤ V` using `mIntNonneg A _ (fun _ => hO') (fun _ => hOp') _ fun _ => zero_le_one`. Use `⟨max V (C * (K + 2) ^ e), fun T hT => ?_⟩` and prove the remaining obligations.

Use `choose θ u hTe hθ hθ1 hθ2 hu hub hc hps using hT`. Take `rfl : T = fun i => θ i + LocPot.ofFun (u i)` from `funext hTe`. Use `set T : Fin e → LocPot X := fun i => θ i + LocPot.ofFun (u i) with hTd`. Establish `hlog : ∀ R, Real.exp 1 ≤ R → 1 ≤ Real.log R` using `fun R hR => (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hR)).2 hR`. Establish `hud : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ContDiffAt ℝ 2 (u i ∘ (A.chart j).symm) y` using `fun i j y hy hn => smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy hn`.

Establish `hTS : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w, leviAt A (T i) j y w ≤ leviAt A (Om.rsmul K) j y w + levi (u i ∘ (A.chart j).symm) y w`. Introduce `i j y hy hn w`. Establish `a1` using `leviAt_nonneg (hθ2 i) j hy w`. Rewrite `a1` using `[leviAt_add hO' (isPotentialRsmul A _ _ (hθ i)) j hy, leviAt_rsmul (θ i)]`. Simplify using `only [hTd]`.

Rewrite using `[leviAt_add_ofFun (hθ i) j hy (hud i j y hy hn)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htr : ∀ R, Real.exp 1 ≤ R → ∀ i, ∃ v : X → ℝ, (A.Smooth v ∧ (∀ x, -(K * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧ IsPsh A (Om.rsmul K + LocPot.ofFun v)) ∧ ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → ∀ w, leviAt A (Om.rsmul K + LocPot.ofFun v) j y w = levi …`. Introduce `R hR i`. Take `⟨v, η, h1, h2, h3, -, -, h6, -⟩` from `trunc (M := K * Real.log R + 2) (u := u i) (by nlinarith [hlog R hR]) hZ hZ0 hO' hOp' (hu i) (fun x hx => (hub i x hx).2) (fun j y hy hn w => (hps i j y hy hn w).trans (hTS i j y hy hn w)) (hc i)`.

Use `⟨v, ⟨h1, h3, h2⟩, fun j y hy hn w => ?_⟩` and prove the remaining obligations. Rewrite using `[leviAt_add_ofFun hO' j hy (smoothOn_contDiffAt isOpen_univ h1 j hy trivial), ← levi_sub_const (u i ∘ (A.chart j).symm) η]`. Use `congr 1`. Apply `levi_congr` to reduce the goal to its premises. Use `filter_upwards [((A.chart j).isOpen_inter_preimage_symm (isOpen_sub hZ hr R)).mem_nhds ⟨hy, hn⟩] with z hz`.

Use `h6 _ hz.2.1 ?_` and prove the remaining obligations. Establish `a1` using `(hub i _ hz.2.1).1`. Establish `a2 : Real.log (r ((A.chart j).symm z)) ≤ Real.log R` using `Real.log_le_log ((Real.exp_pos 1).trans_le (hre _ hz.2.1)) hz.2.2.le`. Use the polynomial consequences of the given equalities and inequalities. Use `choose! v hv hvl using htr`.

Use `set Ψ : ℝ → Fin e → LocPot X := fun R i => Om.rsmul K + LocPot.ofFun (v R i) with hΨ`. Establish `hΨ1 : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPotential A (Ψ R i)` using `fun R hR i => isPotentialAdd A _ _ hO' (isPotential_ofFun A _ (hv R hR i).1)`. Establish `hΨ2 : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPsh A (Ψ R i)` using `fun R hR i => (hv R hR i).2.2`. Establish `hΨV : ∀ R, Real.exp 1 ≤ R → mInt A (Ψ R) (fun _ => 1) = V` using `fun R hR => massIndep A _ (v R) (fun _ => hO') fun i => (hv R hR i).1`. Establish `hΨm : ∀ R, Real.exp 1 ≤ R → maMeasure A (Ψ R) Set.univ = ENNReal.ofReal V` using `fun R hR => by`.

Rewrite using `[mass_univ _ (hΨ1 R hR) (hΨ2 R hR), hΨV R hR]`. Establish `hTd2 : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ContDiffAt ℝ 2 ((T i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y` using `fun i j y hy hn => (potSmoothAt A _ (hθ i) _ j ⟨hy, (θ i).mem_U _⟩).add (hud i j y hy hn)`. Establish `hΨd : ∀ R, Real.exp 1 ≤ R → ∀ i j, ∀ y ∈ (A.chart j).target, ContDiffAt ℝ 2 ((Ψ R i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y` using `fun R hR i j y hy => potSmoothAt A _ (hΨ1 R hR i) _ j ⟨hy, (Ψ R i).mem_U _⟩`. Establish `hT0 : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Zᶜ → 0 ≤ locDens A T j y` using `fun j y hy hn => (maDens_mono_pt _ _ y (fun i => hTd2 i j y hy hn) (fun i => hTd2 i j y hy hn) (fun i w => hps i j y hy hn w) fun i w => le_rfl).1`. Establish `hTΨ : ∀ R, Real.exp 1 ≤ R → ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → locDens A T j y ≤ locDens A (Ψ R) j y` using `fun R hR j y hy hn => (maDens_mono_pt _ _ y (fun i => hTd2 i j y hy hn.1) (fun i => hΨd R hR i j y hy) (fun i w => hps i j y hy hn.1 w) fun i w => (hTS i j y hy hn.1 w).trans (hvl R hR i j y hy hn w).ge).2`.

Establish `hΨΨ : ∀ R R', Real.exp 1 ≤ R → R ≤ R' → ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → locDens A (Ψ R) j y ≤ locDens A (Ψ R') j y` using `fun R R' hR h j y hy hn => (maDens_mono_pt _ _ y (fun i => hΨd R hR i j y hy) (fun i => hΨd R' (hR.trans h) i j y hy) (fun i w => leviAt_nonneg (hΨ2 R hR i) j hy w) fun i w => (hvl R hR i j y hy hn w).le.trans (hvl R' (hR.trans h) i j y hy ⟨hn.1, hn.2.trans_le h⟩ w).ge).2`. Establish `hTc` using `locDens_contOn hZ hθ hu hps`. Establish `hn : ∀ (R : ℝ) (n : ℕ), R ≤ R + n` using `fun R n => le_add_of_nonneg_right n.cast_nonneg`. Establish `hcut : cut Z Set.univ (fun _ => (1 : ℝ)) = Zᶜ.indicator fun _ => 1`. Unfold `cut`.

Rewrite using `[Set.univ_inter]`. Use `⟨?_, ?_, fun R hR => ?_⟩` and prove the remaining obligations. Rewrite using `[hcut]`. Conclude with `mIntegrable_ind hZ.isOpen_compl hTc hT0 _ (fun n => isOpen_sub hZ hr _) (monotone_sub Z r (Real.exp 1)) (iUnion_sub Z r _) (fun n => Ψ (Real.exp 1 + n)) (fun n => hΨ1 _ (hn _ n)) (fun n => hΨ2 _ (hn _ n)) (fun n => hTΨ _ (hn _ n)) fun n => (hΨV _ (hn _ n)).le`. Rewrite using `[hcut]`.

Use `(mInt_ind_le hZ.isOpen_compl hZ.isOpen_compl.measurableSet le_rfl hTc hT0 hV0 ?_).trans (le_max_left _ _)` and prove the remaining obligations. Rewrite using `[← iUnion_sub Z r (Real.exp 1), (monotone_sub Z r _).measure_iUnion]`. Use `iSup_le fun n => ?_` and prove the remaining obligations. Conclude with `(maMeasure_mono_on T _ (isOpen_sub hZ hr _).measurableSet (hTΨ _ (hn _ n))).trans ((measure_mono (Set.subset_univ _)).trans (hΨm _ (hn _ n)).le)`. Establish `hR0 : 0 < R` using `(Real.exp_pos 1).trans_le hR`.

Establish `hE : {x | R ≤ r x} ∩ Zᶜ = ⋃ n : ℕ, ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R})`. Rewrite using `[← Set.iUnion_diff, iUnion_sub]`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_diff, not_and, not_lt]`. The claim follows by propositional logic.

Establish `hm : ∀ n : ℕ, MeasurableSet ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R})` using `fun n => (isOpen_sub hZ hr _).measurableSet.diff (isOpen_sub hZ hr _).measurableSet`. Establish `hmR` using `(isOpen_sub hZ hr R).measurableSet`. Establish `hl` using `hlog R hR`. Establish `hM : 1 ≤ K * Real.log R + 2` using `by nlinarith`. Unfold `cut`.

Use `(mInt_ind_le (C := C * (K * Real.log R + 2) ^ e / R) hZ.isOpen_compl (hE ▸ MeasurableSet.iUnion hm) Set.inter_subset_right hTc hT0 (by positivity) ?_).trans ?_` and prove the remaining obligations. Rewrite using `[hE, Monotone.measure_iUnion fun n m h => Set.diff_subset_diff_left (monotone_sub Z r R h)]`. Use `iSup_le fun n => ?_` and prove the remaining obligations. Use `(maMeasure_mono_on T (Ψ (R + n)) (hm n) fun j y hy h => hTΨ _ (hR.trans (hn R n)) j y hy h.1).trans ?_` and prove the remaining obligations. Use `le_trans ?_ (hC (v R) _ R hM hR0 (hv R hR))` and prove the remaining obligations.

Establish `e1` using `measure_add_measure_compl (μ := maMeasure A (Ψ R)) hmR`. Establish `e2` using `measure_add_measure_compl (μ := maMeasure A (Ψ (R + n))) hmR`. Rewrite `e1` using `[hΨm R hR]`. Rewrite `e2` using `[hΨm _ (hR.trans (hn R n))]`. Establish `e3` using `maMeasure_mono_on (Ψ R) (Ψ (R + n)) hmR (hΨΨ R _ hR (hn R n))`.

Establish `e4 : maMeasure A (Ψ R) {x | x ∉ Z ∧ r x < R} ≠ ⊤` using `ne_top_of_le_ne_top ENNReal.ofReal_ne_top (e1 ▸ le_self_add)`. Use `(measure_mono (Set.diff_subset_compl _ _)).trans ?_` and prove the remaining obligations. Use `(ENNReal.add_le_add_iff_left e4).1 ?_` and prove the remaining obligations. Rewrite using `[e1, ← e2]`. Use `gcongr`.

Use `div_le_div_of_nonneg_right ?_ hR0.le` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Use `_ = C * (K + 2) ^ e * Real.log R ^ e := by rw [mul_pow, mul_assoc]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)`.
-/
theorem shellMass : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, ∀ T : Fin e → LocPot X, (∀ i, ListForm A Z r Om K (T i)) → MIntegrable A T (cut Z Set.univ fun _ => 1) ∧ mInt A T (cut Z Set.univ fun _ => 1) ≤ C ∧ ∀ R : ℝ, Real.exp 1 ≤ R → mInt A T (cut Z {x | R ≤ r x} fun _ => 1) ≤ C * Real.log R ^ e / R := by
  intro e X _ _ _ A Z r Om hB K hK
  borelize X
  obtain ⟨C, hC0, hC⟩ := cheb hB hK
  obtain ⟨hZ, hZ0, hO, hOpos, hr, hre, hb, hri, -⟩ := hB
  have hOp := isPsh_of_isPosPot hOpos
  have hO' : IsPotential A (Om.rsmul K) := isPotentialRsmul A K Om hO
  have hOp' : IsPsh A (Om.rsmul K) := isPshRsmul A K Om (by linarith) hO hOp
  set V := mInt A (fun _ => Om.rsmul K) fun _ => 1 with hV
  have hV0 : 0 ≤ V := mIntNonneg A _ (fun _ => hO') (fun _ => hOp') _ fun _ => zero_le_one
  refine ⟨max V (C * (K + 2) ^ e), fun T hT => ?_⟩
  choose θ u hTe hθ hθ1 hθ2 hu hub hc hps using hT
  obtain rfl : T = fun i => θ i + LocPot.ofFun (u i) := funext hTe
  set T : Fin e → LocPot X := fun i => θ i + LocPot.ofFun (u i) with hTd
  have hlog : ∀ R, Real.exp 1 ≤ R → 1 ≤ Real.log R := fun R hR =>
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hR)).2 hR
  have hud : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z →
      ContDiffAt ℝ 2 (u i ∘ (A.chart j).symm) y := fun i j y hy hn =>
    smoothOn_contDiffAt hZ.isOpen_compl (hu i) j hy hn
  have hTS : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z → ∀ w,
      leviAt A (T i) j y w ≤ leviAt A (Om.rsmul K) j y w + levi (u i ∘ (A.chart j).symm) y w := by
    intro i j y hy hn w
    have a1 := leviAt_nonneg (hθ2 i) j hy w
    rw [leviAt_add hO' (isPotentialRsmul A _ _ (hθ i)) j hy, leviAt_rsmul (θ i)] at a1
    simp only [hTd]
    rw [leviAt_add_ofFun (hθ i) j hy (hud i j y hy hn)]
    linarith
  have htr : ∀ R, Real.exp 1 ≤ R → ∀ i, ∃ v : X → ℝ, (A.Smooth v ∧
      (∀ x, -(K * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧ IsPsh A (Om.rsmul K + LocPot.ofFun v)) ∧
      ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → ∀ w,
        leviAt A (Om.rsmul K + LocPot.ofFun v) j y w =
          leviAt A (Om.rsmul K) j y w + levi (u i ∘ (A.chart j).symm) y w := by
    intro R hR i
    obtain ⟨v, η, h1, h2, h3, -, -, h6, -⟩ := trunc (M := K * Real.log R + 2) (u := u i)
      (by nlinarith [hlog R hR]) hZ hZ0 hO' hOp' (hu i) (fun x hx => (hub i x hx).2)
      (fun j y hy hn w => (hps i j y hy hn w).trans (hTS i j y hy hn w)) (hc i)
    refine ⟨v, ⟨h1, h3, h2⟩, fun j y hy hn w => ?_⟩
    rw [leviAt_add_ofFun hO' j hy (smoothOn_contDiffAt isOpen_univ h1 j hy trivial),
      ← levi_sub_const (u i ∘ (A.chart j).symm) η]
    congr 1
    apply levi_congr
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm (isOpen_sub hZ hr R)).mem_nhds ⟨hy, hn⟩]
      with z hz
    refine h6 _ hz.2.1 ?_
    have a1 := (hub i _ hz.2.1).1
    have a2 : Real.log (r ((A.chart j).symm z)) ≤ Real.log R :=
      Real.log_le_log ((Real.exp_pos 1).trans_le (hre _ hz.2.1)) hz.2.2.le
    nlinarith
  choose! v hv hvl using htr
  set Ψ : ℝ → Fin e → LocPot X := fun R i => Om.rsmul K + LocPot.ofFun (v R i) with hΨ
  have hΨ1 : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPotential A (Ψ R i) := fun R hR i =>
    isPotentialAdd A _ _ hO' (isPotential_ofFun A _ (hv R hR i).1)
  have hΨ2 : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPsh A (Ψ R i) := fun R hR i => (hv R hR i).2.2
  have hΨV : ∀ R, Real.exp 1 ≤ R → mInt A (Ψ R) (fun _ => 1) = V := fun R hR =>
    massIndep A _ (v R) (fun _ => hO') fun i => (hv R hR i).1
  have hΨm : ∀ R, Real.exp 1 ≤ R → maMeasure A (Ψ R) Set.univ = ENNReal.ofReal V := fun R hR => by
    rw [mass_univ _ (hΨ1 R hR) (hΨ2 R hR), hΨV R hR]
  have hTd2 : ∀ i j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∉ Z →
      ContDiffAt ℝ 2 ((T i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y := fun i j y hy hn =>
    (potSmoothAt A _ (hθ i) _ j ⟨hy, (θ i).mem_U _⟩).add (hud i j y hy hn)
  have hΨd : ∀ R, Real.exp 1 ≤ R → ∀ i j, ∀ y ∈ (A.chart j).target,
      ContDiffAt ℝ 2 ((Ψ R i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) y := fun R hR i j y hy =>
    potSmoothAt A _ (hΨ1 R hR i) _ j ⟨hy, (Ψ R i).mem_U _⟩
  have hT0 : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Zᶜ → 0 ≤ locDens A T j y :=
    fun j y hy hn => (maDens_mono_pt _ _ y (fun i => hTd2 i j y hy hn) (fun i => hTd2 i j y hy hn)
      (fun i w => hps i j y hy hn w) fun i w => le_rfl).1
  have hTΨ : ∀ R, Real.exp 1 ≤ R → ∀ j, ∀ y ∈ (A.chart j).target,
      (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → locDens A T j y ≤ locDens A (Ψ R) j y :=
    fun R hR j y hy hn => (maDens_mono_pt _ _ y (fun i => hTd2 i j y hy hn.1) (fun i => hΨd R hR i j y hy)
      (fun i w => hps i j y hy hn.1 w) fun i w =>
        (hTS i j y hy hn.1 w).trans (hvl R hR i j y hy hn w).ge).2
  have hΨΨ : ∀ R R', Real.exp 1 ≤ R → R ≤ R' → ∀ j, ∀ y ∈ (A.chart j).target,
      (A.chart j).symm y ∈ {x | x ∉ Z ∧ r x < R} → locDens A (Ψ R) j y ≤ locDens A (Ψ R') j y :=
    fun R R' hR h j y hy hn => (maDens_mono_pt _ _ y (fun i => hΨd R hR i j y hy)
      (fun i => hΨd R' (hR.trans h) i j y hy) (fun i w => leviAt_nonneg (hΨ2 R hR i) j hy w) fun i w =>
        (hvl R hR i j y hy hn w).le.trans (hvl R' (hR.trans h) i j y hy ⟨hn.1, hn.2.trans_le h⟩ w).ge).2
  have hTc := locDens_contOn hZ hθ hu hps
  have hn : ∀ (R : ℝ) (n : ℕ), R ≤ R + n := fun R n => le_add_of_nonneg_right n.cast_nonneg
  have hcut : cut Z Set.univ (fun _ => (1 : ℝ)) = Zᶜ.indicator fun _ => 1 := by
    unfold cut
    rw [Set.univ_inter]
  refine ⟨?_, ?_, fun R hR => ?_⟩
  · rw [hcut]
    exact mIntegrable_ind hZ.isOpen_compl hTc hT0 _ (fun n => isOpen_sub hZ hr _)
      (monotone_sub Z r (Real.exp 1)) (iUnion_sub Z r _) (fun n => Ψ (Real.exp 1 + n))
      (fun n => hΨ1 _ (hn _ n)) (fun n => hΨ2 _ (hn _ n)) (fun n => hTΨ _ (hn _ n))
      fun n => (hΨV _ (hn _ n)).le
  · rw [hcut]
    refine (mInt_ind_le hZ.isOpen_compl hZ.isOpen_compl.measurableSet le_rfl hTc hT0 hV0 ?_).trans
      (le_max_left _ _)
    rw [← iUnion_sub Z r (Real.exp 1), (monotone_sub Z r _).measure_iUnion]
    refine iSup_le fun n => ?_
    exact (maMeasure_mono_on T _ (isOpen_sub hZ hr _).measurableSet (hTΨ _ (hn _ n))).trans
      ((measure_mono (Set.subset_univ _)).trans (hΨm _ (hn _ n)).le)
  · have hR0 : 0 < R := (Real.exp_pos 1).trans_le hR
    have hE : {x | R ≤ r x} ∩ Zᶜ = ⋃ n : ℕ, ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) := by
      rw [← Set.iUnion_diff, iUnion_sub]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_diff, not_and, not_lt]
      tauto
    have hm : ∀ n : ℕ, MeasurableSet ({x | x ∉ Z ∧ r x < R + n} \ {x | x ∉ Z ∧ r x < R}) := fun n =>
      (isOpen_sub hZ hr _).measurableSet.diff (isOpen_sub hZ hr _).measurableSet
    have hmR := (isOpen_sub hZ hr R).measurableSet
    have hl := hlog R hR
    have hM : 1 ≤ K * Real.log R + 2 := by nlinarith
    unfold cut
    refine (mInt_ind_le (C := C * (K * Real.log R + 2) ^ e / R) hZ.isOpen_compl
      (hE ▸ MeasurableSet.iUnion hm) Set.inter_subset_right hTc hT0 (by positivity) ?_).trans ?_
    · rw [hE, Monotone.measure_iUnion fun n m h => Set.diff_subset_diff_left (monotone_sub Z r R h)]
      refine iSup_le fun n => ?_
      refine (maMeasure_mono_on T (Ψ (R + n)) (hm n)
        fun j y hy h => hTΨ _ (hR.trans (hn R n)) j y hy h.1).trans ?_
      refine le_trans ?_ (hC (v R) _ R hM hR0 (hv R hR))
      have e1 := measure_add_measure_compl (μ := maMeasure A (Ψ R)) hmR
      have e2 := measure_add_measure_compl (μ := maMeasure A (Ψ (R + n))) hmR
      rw [hΨm R hR] at e1
      rw [hΨm _ (hR.trans (hn R n))] at e2
      have e3 := maMeasure_mono_on (Ψ R) (Ψ (R + n)) hmR (hΨΨ R _ hR (hn R n))
      have e4 : maMeasure A (Ψ R) {x | x ∉ Z ∧ r x < R} ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (e1 ▸ le_self_add)
      refine (measure_mono (Set.diff_subset_compl _ _)).trans ?_
      refine (ENNReal.add_le_add_iff_left e4).1 ?_
      rw [e1, ← e2]
      gcongr
    · refine div_le_div_of_nonneg_right ?_ hR0.le
      calc C * (K * Real.log R + 2) ^ e ≤ C * ((K + 2) * Real.log R) ^ e := by
            gcongr
            nlinarith
        _ = C * (K + 2) ^ e * Real.log R ^ e := by rw [mul_pow, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end GlobalTheory.ShellMass
