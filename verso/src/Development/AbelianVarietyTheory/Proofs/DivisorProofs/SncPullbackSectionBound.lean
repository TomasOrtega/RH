import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableAbsLogNormSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackHolomorphic
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.LogNormPullbackBound

noncomputable section

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Establish `h` using `hs.2 w x w ⟨L.mem_U w, hw⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite `h` using `[h0, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne')`.

Introduce `h0`. Rewrite `h` using `[h0, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne')`.
-/
theorem sec_zero_iff (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ) (hs : IsSection A L s)
    (x w : X) (hw : w ∈ L.U x) : s w w = 0 ↔ s x w = 0 := by
  have h := hs.2 w x w ⟨L.mem_U w, hw⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne')

/- English proof (translation)
Establish `hs'` using `GlobalTheory.isSection_pullback_holoMap d n X Y A B μ hμ L s hs`. Introduce `y`. Use `⟨μ ⁻¹' L.U (μ y), (L.isOpen_U (μ y)).preimage hμ.1, L.mem_U (μ y), 1, fun _ w => s (μ y) (μ w), fun _ => hs'.1 y, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_sep_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, hw⟩`. Conclude with `⟨hw, fun _ => (sec_zero_iff A L s hs (μ y) (μ w) hw).1 h0⟩`. Introduce and unpack `⟨hw, h0⟩`. Conclude with `⟨(sec_zero_iff A L s hs (μ y) (μ w) hw).2 (h0 0), hw⟩`.
-/
theorem isAnalyticSubset_zero (A : FinHolAtlas d X) (B : FinHolAtlas n Y) (μ : Y → X)
    (hμ : HoloMap B A μ) (L : LocPot X) (s : X → X → ℂ) (hs : IsSection A L s) :
    B.IsAnalyticSubset {y | s (μ y) (μ y) = 0} := by
  have hs' := GlobalTheory.isSection_pullback_holoMap d n X Y A B μ hμ L s hs
  intro y
  refine ⟨μ ⁻¹' L.U (μ y), (L.isOpen_U (μ y)).preimage hμ.1, L.mem_U (μ y), 1,
    fun _ w => s (μ y) (μ w), fun _ => hs'.1 y, ?_⟩
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_sep_iff]
  constructor
  · rintro ⟨h0, hw⟩
    exact ⟨hw, fun _ => (sec_zero_iff A L s hs (μ y) (μ w) hw).1 h0⟩
  · rintro ⟨hw, h0⟩
    exact ⟨(sec_zero_iff A L s hs (μ y) (μ w) hw).2 (h0 0), hw⟩

def sncMonomial {r : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) (z : Fin n → ℂ) : ℂ :=
  ∏ k, (match σ k with
    | some i => z i ^ m k
    | none => 1)

/- English proof (translation)
Establish `: ∀ k ∈ (Finset.univ : Finset (Fin r)), AnalyticOnNhd ℂ (fun z : Fin n → ℂ => (match σ k with`. Consider the case `some i => z i ^ m k`. Consider the case `none => 1)) Set.univ := by`. Introduce `k _`. Break down `σ k with _ | i` into its components or cases.

Conclude with `analyticOnNhd_const`. Introduce `z _`. Conclude with `((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).pow _`. Establish `h` using `Finset.analyticOnNhd_prod Finset.univ this`. Introduce `z hz`.

Use `(h z hz).congr (Filter.Eventually.of_forall fun z' => ?_)` and prove the remaining obligations. Unfold `sncMonomial`. Rewrite using `[Finset.prod_apply]`.
-/
theorem sncMonomial_analytic {r : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) :
    AnalyticOnNhd ℂ (sncMonomial σ m) Set.univ := by
  have : ∀ k ∈ (Finset.univ : Finset (Fin r)), AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      (match σ k with
        | some i => z i ^ m k
        | none => 1)) Set.univ := by
    intro k _
    rcases σ k with _ | i
    · exact analyticOnNhd_const
    · intro z _
      exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).pow _
  have h := Finset.analyticOnNhd_prod Finset.univ this
  intro z hz
  refine (h z hz).congr (Filter.Eventually.of_forall fun z' => ?_)
  unfold sncMonomial
  rw [Finset.prod_apply]

/- English proof (translation)
Unfold `sncMonomial`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases σ k with _ | i <;> simp`.
-/
theorem sncMonomial_one {r : ℕ} (σ : Fin r → Option (Fin n)) (m : Fin r → ℕ) :
    sncMonomial σ m (fun _ => 1) = 1 := by
  unfold sncMonomial
  refine Finset.prod_eq_one fun k _ => ?_
  rcases σ k with _ | i <;> simp

/- English proof (translation)
Use `Set.eq_empty_of_forall_notMem fun y0 hy0 => ?_` and prove the remaining obligations. Take `⟨ψ, -, hy0ψ, hsrc, σ, -, -, u, -, hu, hfac⟩` from `hsnc y0`. Establish `hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (interior {y | s (μ y) (μ y) = 0} ∩ ψ.source))` using `ψ.isOpen_inter_preimage_symm (isOpen_interior.inter ψ.open_source)`. Establish `hm : ψ y0 ∈ ψ.target ∩ ψ.symm ⁻¹' (interior {y | s (μ y) (μ y) = 0} ∩ ψ.source)`. Use `⟨ψ.map_source hy0ψ, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, ψ.left_inv hy0ψ]`. Conclude with `⟨hy0, hy0ψ⟩`. Establish `hev : sncMonomial σ m₀ =ᶠ[nhds (ψ y0)] 0` using `by filter_upwards [hO.mem_nhds hm] with z hz`. Take `⟨hzt, hzi, hzs⟩` from `hz`. Establish `hw : s (μ (ψ.symm z)) (μ (ψ.symm z)) = 0` using `(interior_subset hzi : ψ.symm z ∈ {y | s (μ y) (μ y) = 0})`.

Establish `hw2 : s (μ y0) (μ (ψ.symm z)) = 0` using `(sec_zero_iff A L s hs (μ y0) (μ (ψ.symm z)) (hsrc hzs)).1 hw`. Establish `hf` using `hfac _ hzs`. Simplify using `only at hf`. Rewrite `hw2` using `[hf]`. Establish `h3` using `(mul_eq_zero.1 hw2).resolve_left (hu _ hzs)`.

Simplify using `only [ψ.right_inv hzt] at h3`. Use `show sncMonomial σ m₀ z = 0`. Rewrite using `[← h3]`. Unfold `sncMonomial`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `rcases σ k with _ | i <;> rfl`. Establish `h1` using `(sncMonomial_analytic σ m₀).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ _) hev (Set.mem_univ (fun _ => (1 : ℂ)))`. Rewrite `h1` using `[sncMonomial_one]`. Simplify using `at h1`.
-/
theorem interior_zero_eq_empty (A : FinHolAtlas d X) (B : FinHolAtlas n Y) (μ : Y → X)
    (hμ : HoloMap B A μ) (L : LocPot X) (s : X → X → ℂ) (hs : IsSection A L s) {r : ℕ}
    (m₀ : Fin r → ℕ) (W : Fin r → Set Y)
    (hsnc : IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) m₀ W) :
    interior {y | s (μ y) (μ y) = 0} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y0 hy0 => ?_
  obtain ⟨ψ, -, hy0ψ, hsrc, σ, -, -, u, -, hu, hfac⟩ := hsnc y0
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (interior {y | s (μ y) (μ y) = 0} ∩ ψ.source)) :=
    ψ.isOpen_inter_preimage_symm (isOpen_interior.inter ψ.open_source)
  have hm : ψ y0 ∈ ψ.target ∩ ψ.symm ⁻¹' (interior {y | s (μ y) (μ y) = 0} ∩ ψ.source) := by
    refine ⟨ψ.map_source hy0ψ, ?_⟩
    simp only [Set.mem_preimage, ψ.left_inv hy0ψ]
    exact ⟨hy0, hy0ψ⟩
  have hev : sncMonomial σ m₀ =ᶠ[nhds (ψ y0)] 0 := by
    filter_upwards [hO.mem_nhds hm] with z hz
    obtain ⟨hzt, hzi, hzs⟩ := hz
    have hw : s (μ (ψ.symm z)) (μ (ψ.symm z)) = 0 := (interior_subset hzi : ψ.symm z ∈ {y | s (μ y) (μ y) = 0})
    have hw2 : s (μ y0) (μ (ψ.symm z)) = 0 :=
      (sec_zero_iff A L s hs (μ y0) (μ (ψ.symm z)) (hsrc hzs)).1 hw
    have hf := hfac _ hzs
    simp only at hf
    rw [hf] at hw2
    have h3 := (mul_eq_zero.1 hw2).resolve_left (hu _ hzs)
    simp only [ψ.right_inv hzt] at h3
    show sncMonomial σ m₀ z = 0
    rw [← h3]
    unfold sncMonomial
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases σ k with _ | i <;> rfl
  have h1 := (sncMonomial_analytic σ m₀).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ _) hev (Set.mem_univ (fun _ => (1 : ℂ)))
  rw [sncMonomial_one] at h1
  simp at h1

end

end GlobalTheory.LogNormPullbackBound

namespace GlobalTheory.LogNormPullbackBound

section

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Establish `hZ : {y | s (μ y) (μ y) = 0} = (fun y => normSec L s (μ y)) ⁻¹' {0}`. Use extensionality with `y`. Simplify using `[normSec, (Real.exp_pos _).ne']`. Establish `hZm : MeasurableSet {y | s (μ y) (μ y) = 0}`. Rewrite using `[hZ]`.

Conclude with `(((GlobalTheory.AbsLogNormMeas.continuous_normSec A L s hL hs).comp hμ.1).measurable) (measurableSet_singleton 0)`. Establish `hnull` using `analyticNull B _ (isAnalyticSubset_zero A B μ hμ L s hs) (interior_zero_eq_empty A B μ hμ L s hs m₀ W hsnc)`. Unfold `maMeasure`. Use `split_ifs with h`. Rewrite using `[Measure.coe_finset_sum, Finset.sum_apply]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hae : AEMeasurable (B.chart j).symm ((volume.restrict (B.chart j).target).withDensity fun y => ENNReal.ofReal (h.some.χ j ((B.chart j).symm y) * locDens B Φ j y))` using `((B.chart j).continuousOn_symm.aemeasurable (B.chart j).open_target.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)`. Rewrite using `[Measure.map_apply_of_aemeasurable hae hZm]`. Use `withDensity_absolutelyContinuous _ _ ?_` and prove the remaining obligations. Establish `h0` using `hnull j`.

Rewrite `h0` using `[Set.inter_comm, (B.chart j).image_source_inter_eq']`. Rewrite using `[Measure.restrict_apply' (B.chart j).open_target.measurableSet, Set.inter_comm]`. Conclude with `h0`. Simplify using the standard rewrite rules.
-/
theorem maMeasure_zero_null (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ)
    (hL : IsPotential A L) (hs : IsSection A L s) (B : FinHolAtlas n Y) (μ : Y → X)
    (hμ : HoloMap B A μ) {r : ℕ} (W : Fin r → Set Y) (m₀ : Fin r → ℕ)
    (hsnc : IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) m₀ W)
    [MeasurableSpace Y] [BorelSpace Y] (Φ : Fin n → LocPot Y) :
    maMeasure B Φ {y | s (μ y) (μ y) = 0} = 0 := by
  have hZ : {y | s (μ y) (μ y) = 0} = (fun y => normSec L s (μ y)) ⁻¹' {0} := by
    ext y
    simp [normSec, (Real.exp_pos _).ne']
  have hZm : MeasurableSet {y | s (μ y) (μ y) = 0} := by
    rw [hZ]
    exact (((GlobalTheory.AbsLogNormMeas.continuous_normSec A L s hL hs).comp hμ.1).measurable)
      (measurableSet_singleton 0)
  have hnull := analyticNull B _ (isAnalyticSubset_zero A B μ hμ L s hs)
    (interior_zero_eq_empty A B μ hμ L s hs m₀ W hsnc)
  unfold maMeasure
  split_ifs with h
  · rw [Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hae : AEMeasurable (B.chart j).symm ((volume.restrict (B.chart j).target).withDensity
        fun y => ENNReal.ofReal (h.some.χ j ((B.chart j).symm y) * locDens B Φ j y)) :=
      ((B.chart j).continuousOn_symm.aemeasurable (B.chart j).open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable hae hZm]
    refine withDensity_absolutelyContinuous _ _ ?_
    have h0 := hnull j
    rw [Set.inter_comm, (B.chart j).image_source_inter_eq'] at h0
    rw [Measure.restrict_apply' (B.chart j).open_target.measurableSet, Set.inter_comm]
    exact h0
  · simp

end

/- English proof (translation)
Introduce `d X _ _ _ A L s hL hs hle n Y _ _ _ B μ hμ r W m₀ hsnc _ _ Φ hΦ hpsh`. Establish `hL' : IsPotential B (L.pullback μ hμ.1)` using `isPotentialPullback A B μ hμ L hL`. Establish `hs'` using `GlobalTheory.isSection_pullback_holoMap d n X Y A B μ hμ L s hs`. Establish `hint` using `logNormIntegrable B (L.pullback μ hμ.1) _ m₀ W hL' hs' hsnc Φ hΦ`. Use `set g : Y → ℝ := fun y => -logNormSec L s (μ y) with hgdef`.

Establish `hgint : MIntegrable B Φ g`. Introduce `j K hK hKc`. Use `(Integrable.neg (hint j K hK hKc)).congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Pi.neg_apply, g, neg_mul]`. Both sides reduce to the same expression.

Establish `hgmeas : Measurable g`. Use `(Real.measurable_log.comp ((GlobalTheory.AbsLogNormMeas.continuous_normSec A L s hL hs).comp hμ.1).measurable).neg` as an intermediate fact. Conclude with `this`. Establish `hlog : ∀ y, logNormSec L s (μ y) ≤ 0` using `fun y => Real.log_nonpos (by positivity) (hle (μ y))`. Establish `hg0 : ∀ y, 0 ≤ g y` using `fun y => neg_nonneg.2 (hlog y)`.

Take `⟨-, hthm⟩` from `maMeasure_thm B Φ hΦ hpsh`. Take `⟨hiff, heq⟩` from `hthm g hgmeas`. Establish `hgI : Integrable g (maMeasure B Φ)` using `hiff.1 hgint`. Rewrite using `[heq hgint, ofReal_integral_eq_lintegral_ofReal hgI (Filter.Eventually.of_forall hg0)]`. Establish `hZ : ∀ᵐ y ∂maMeasure B Φ, s (μ y) (μ y) ≠ 0`.

Rewrite using `[ae_iff]`. Simplify `maMeasure_zero_null A L s hL hs B μ hμ W m₀ hsnc Φ` using `only [ne_eq, not_not]`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [hZ] with y hy`. Simplify using `only [absLogNorm, hy, if_false, g]`.

Rewrite using `[abs_of_nonpos (hlog y)]`.
-/
theorem lintegral_absLogNorm_le : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y)
    (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y) (m₀ : Fin r → ℕ),
    IsSNC B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) m₀ W →
    ∀ [MeasurableSpace Y] [BorelSpace Y] (Φ : Fin n → LocPot Y), (∀ i, IsPotential B (Φ i)) →
    (∀ i, IsPsh B (Φ i)) →
    ∫⁻ y, absLogNorm L s (μ y) ∂maMeasure B Φ ≤
      ENNReal.ofReal (mInt B Φ (fun y => -logNormSec L s (μ y))) := by
  intro d X _ _ _ A L s hL hs hle n Y _ _ _ B μ hμ r W m₀ hsnc _ _ Φ hΦ hpsh
  have hL' : IsPotential B (L.pullback μ hμ.1) := isPotentialPullback A B μ hμ L hL
  have hs' := GlobalTheory.isSection_pullback_holoMap d n X Y A B μ hμ L s hs
  have hint := logNormIntegrable B (L.pullback μ hμ.1) _ m₀ W hL' hs' hsnc Φ hΦ
  set g : Y → ℝ := fun y => -logNormSec L s (μ y) with hgdef
  have hgint : MIntegrable B Φ g := by
    intro j K hK hKc
    refine (Integrable.neg (hint j K hK hKc)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply, g, neg_mul]
    rfl
  have hgmeas : Measurable g := by
    have := (Real.measurable_log.comp
      ((GlobalTheory.AbsLogNormMeas.continuous_normSec A L s hL hs).comp hμ.1).measurable).neg
    exact this
  have hlog : ∀ y, logNormSec L s (μ y) ≤ 0 := fun y =>
    Real.log_nonpos (by positivity) (hle (μ y))
  have hg0 : ∀ y, 0 ≤ g y := fun y => neg_nonneg.2 (hlog y)
  obtain ⟨-, hthm⟩ := maMeasure_thm B Φ hΦ hpsh
  obtain ⟨hiff, heq⟩ := hthm g hgmeas
  have hgI : Integrable g (maMeasure B Φ) := hiff.1 hgint
  rw [heq hgint, ofReal_integral_eq_lintegral_ofReal hgI (Filter.Eventually.of_forall hg0)]
  have hZ : ∀ᵐ y ∂maMeasure B Φ, s (μ y) (μ y) ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using maMeasure_zero_null A L s hL hs B μ hμ W m₀ hsnc Φ
  refine lintegral_mono_ae ?_
  filter_upwards [hZ] with y hy
  simp only [absLogNorm, hy, if_false, g]
  rw [abs_of_nonpos (hlog y)]

end GlobalTheory.LogNormPullbackBound
