import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def LogNormSecLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (x : X) (y : X), IsSection A L s → y ∈ L.U x → s x y ≠ 0 →
      logNormSec L s y = Real.log ‖s x y‖ - L.φ x y

/- English proof (translation)
Introduce `e X _ A L s x y hS hy hs`. Unfold `logNormSec`. Rewrite using `[hS.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.mpr hs) (Real.exp_pos _).ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNormSecLocal : LogNormSecLocalStatement := by
  intro e X _ A L s x y hS hy hs
  unfold logNormSec
  rw [hS.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.mpr hs) (Real.exp_pos _).ne',
    Real.log_exp]
  ring

/- English proof (translation)
Distinguish the cases in `h0 : s x p = 0`. Unfold `logNormSec`. Rewrite using `[hS.2 p x p ⟨L.mem_U p, hp⟩, Set.indicator_apply, if_pos (show p ∈ {q | s x q = 0} from h0), h0]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_apply, if_neg (show p ∉ {q | s x q = 0} from h0), logNormSecLocal A L s x p hS hp h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNormSec_eq_indicator {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hS : IsSection A L s) {x p : X} (hp : p ∈ L.U x) :
    logNormSec L s p = Real.log ‖s x p‖ - L.φ x p + {q | s x q = 0}.indicator (L.φ x) p := by
  by_cases h0 : s x p = 0
  · unfold logNormSec
    rw [hS.2 p x p ⟨L.mem_U p, hp⟩, Set.indicator_apply,
      if_pos (show p ∈ {q | s x q = 0} from h0), h0]
    simp
  · rw [Set.indicator_apply, if_neg (show p ∉ {q | s x q = 0} from h0),
      logNormSecLocal A L s x p hS hp h0]
    ring

/- English proof (translation)
Repeatedly rewrite using `[hg]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, zpow_natCast]`.
-/
theorem prod_option_eq_prod_zpow {e r : ℕ} (σ : Fin r → Option (Fin e)) (m : Fin r → ℕ)
    (w : Fin e → ℂ) (g : Fin r → ℂ) (hg : ∀ k, g k = ∏ i, if σ k = some i then w i ^ m k else 1) :
    ∏ k, g k = ∏ i, w i ^ (((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ)) : ℤ) := by
  simp_rw [hg]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, zpow_natCast]

/- English proof (translation)
Introduce `e X _ _ _ A L s r m W hL hS hSNC Φ hΦ j K hKt hK`. Use `LocallyIntegrableOn.integrableOn_isCompact (fun y0 hy0 => ?_) hK` and prove the remaining obligations. Use `set c := A.chart j with hc`. Establish `hy0t : y0 ∈ c.target` using `hKt hy0`. Take `⟨ψ, hψc, hx0ψ, hψU, σ, -, -, u, hu, hu0, hsu⟩` from `hSNC (c.symm y0)`.

Use `set x0 := c.symm y0 with hx0`. Establish `hNo : IsOpen (c.target ∩ c.symm ⁻¹' ψ.source)` using `c.isOpen_inter_preimage_symm ψ.open_source`. Establish `hy0N : y0 ∈ c.target ∩ c.symm ⁻¹' ψ.source` using `⟨hy0t, hx0ψ⟩`. Take `⟨ε, hε, hεN⟩` from `Metric.isOpen_iff.mp hNo y0 hy0N`. Use `set B := Metric.closedBall y0 (ε / 2) with hB`.

Establish `hBN : B ⊆ c.target ∩ c.symm ⁻¹' ψ.source` using `(Metric.closedBall_subset_ball (by linarith)).trans hεN`. Establish `hBc : IsCompact B` using `isCompact_closedBall y0 (ε / 2)`. Establish `hBm : MeasurableSet B` using `Metric.isClosed_closedBall.measurableSet`. Use `⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩` and prove the remaining obligations. Use `set V := ψ.target ∩ ψ.symm ⁻¹' c.source with hV`.

Establish `hVo : IsOpen V` using `ψ.isOpen_inter_preimage_symm c.open_source`. Establish `hTinvA : AnalyticOnNhd ℂ (c ∘ ψ.symm) V` using `(hψc j).2`. Establish `hTV : ∀ y ∈ c.target ∩ c.symm ⁻¹' ψ.source, ψ (c.symm y) ∈ V ∧ c (ψ.symm (ψ (c.symm y))) = y`. Introduce `y hy`. Use `⟨⟨ψ.map_source hy.2, ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, ψ.left_inv hy.2]`. Conclude with `c.map_target hy.1`. Rewrite using `[ψ.left_inv hy.2, c.right_inv hy.1]`. Use `set m' : Fin e → ℤ := fun i => ((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ) : ℤ) with hm'`. Use `set G : (Fin e → ℂ) → ℝ := fun z => Real.log ‖u (ψ.symm z) * ∏ i, z i ^ m' i‖ with hG`.

Establish `hGloc : LocallyIntegrableOn G V`. Use `hLU e m' V (fun z => u (ψ.symm z)) hVo ?_ (fun z hz => hu0 _ (ψ.map_target hz.1))` and prove the remaining obligations. Introduce `z hz`. Establish `hw : c (ψ.symm z) ∈ c.target ∩ c.symm ⁻¹' ψ.source`. Use `⟨c.map_source hz.2, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, c.left_inv hz.2]`. Conclude with `ψ.map_target hz.1`. Establish `h1 : AnalyticAt ℂ ((u ∘ c.symm) ∘ (c ∘ ψ.symm)) z` using `AnalyticAt.comp (g := u ∘ c.symm) (f := c ∘ ψ.symm) (hu j _ hw) (hTinvA z hz)`. Use `(h1.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt` and prove the remaining obligations. Use `filter_upwards [hVo.mem_nhds hz] with w hw`.

Simplify using `[Function.comp, c.left_inv hw.2]`. Establish `hTc : ContinuousOn (fun y => ψ (c.symm y)) (c.target ∩ c.symm ⁻¹' ψ.source)` using `ψ.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left) (fun y hy => hy.2)`. Use `set C := (fun y => ψ (c.symm y)) '' B with hC`. Establish `hCc : IsCompact C` using `hBc.image_of_continuousOn (hTc.mono hBN)`. Establish `hCm : MeasurableSet C` using `hCc.isClosed.measurableSet`.

Establish `hCV : C ⊆ V`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `(hTV y (hBN hy)).1`. Establish `hCB : (c ∘ ψ.symm) '' C = B`. Rewrite using `[hC, Set.image_image]`.

Use `conv_rhs => rw [← Set.image_id B]`. Conclude with `Set.image_congr fun y hy => (hTV y (hBN hy)).2`. Establish `hinj : Set.InjOn (c ∘ ψ.symm) C`. Introduce and unpack `_ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h`. Simplify using `only [Function.comp_apply] at h`.

Rewrite `h` using `[(hTV y (hBN hy)).2, (hTV y' (hBN hy')).2]`. Rewrite using `[h]`. Establish `hderR : ∀ z ∈ V, DifferentiableAt ℝ (c ∘ ψ.symm) z` using `fun z hz => (hTinvA z hz).differentiableAt.restrictScalars ℝ`. Establish `hdetc : ContinuousOn (fun z => |(fderiv ℝ (c ∘ ψ.symm) z).det|) C`. Establish `h1 : ContDiffOn ℝ 1 (c ∘ ψ.symm) V` using `(hTinvA.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ`.

Conclude with `((ContinuousLinearMap.continuous_det.comp_continuousOn (h1.continuousOn_fderiv_of_isOpen hVo le_rfl)).abs).mono hCV`. Establish `hGT : IntegrableOn (fun y => G (ψ (c.symm y))) B`. Establish `hiff` using `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hCm (f := c ∘ ψ.symm) (f' := fun z => fderiv ℝ (c ∘ ψ.symm) z) (fun z hz => (hderR z (hCV hz)).hasFDerivAt.hasFDerivWithinAt) hinj (fun y => G (ψ (c.symm y)))`. Rewrite `hiff` using `[hCB]`. Use `hiff.mpr ?_` and prove the remaining obligations.

Use `IntegrableOn.congr_fun ((hGloc.integrableOn_compact_subset hCV hCc).continuousOn_smul hdetc hCc) ?_ hCm` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `h` using `(hTV y (hBN hy)).2`. Simplify using `only [Function.comp_apply, h]`. Establish `hdB : ContinuousOn (locDens A Φ j) B` using `(hD A Φ hΦ j).mono (hBN.trans Set.inter_subset_left)`.

Establish `hsub : c.target ∩ c.symm ⁻¹' ψ.source ⊆ c.target ∩ c.symm ⁻¹' L.U x0` using `fun y hy => ⟨hy.1, hψU hy.2⟩`. Establish `hφB : ContinuousOn (fun y => L.φ x0 (c.symm y)) B` using `((hL.1 x0 j).continuousOn.mono hsub).mono hBN`. Establish `hsB : ContinuousOn (fun y => s x0 (c.symm y)) B` using `((hS.1 x0 j).continuousOn.mono hsub).mono hBN`. Use `set Z := B ∩ (fun y => s x0 (c.symm y)) ⁻¹' {0} with hZ`. Establish `hZm : MeasurableSet Z` using `(hsB.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton).measurableSet`.

Establish `h1 : IntegrableOn (fun y => G (ψ (c.symm y)) * locDens A Φ j y) B` using `hGT.mul_continuousOn hdB hBc`. Establish `h2 : IntegrableOn (fun y => L.φ x0 (c.symm y) * locDens A Φ j y) B` using `(hφB.mul hdB).integrableOn_compact hBc`. Establish `h3` using `h2.indicator hZm`. Use `IntegrableOn.congr_fun (Integrable.add (Integrable.sub h1 h2) h3) ?_ hBm` and prove the remaining obligations. Introduce `y hy`.

Establish `hyN` using `hBN hy`. Establish `hp : c.symm y ∈ L.U x0` using `hψU hyN.2`. Establish `hprod : ∀ w : Fin e → ℂ, (∏ k, (match σ k with`. Consider the case `some i => w i ^ m k`. Consider the case `none => 1)) = ∏ i, w i ^ m' i := by`.

Introduce `w`. Apply `prod_option_eq_prod_zpow` to reduce the goal to its premises. Introduce `k`. Apply the tactic sequence `split <;> simp_all`. Establish `hlog : Real.log ‖s x0 (c.symm y)‖ = G (ψ (c.symm y))` using `by show _ = Real.log ‖u (ψ.symm (ψ (c.symm y))) * ∏ i, (ψ (c.symm y)) i ^ m' i‖`.

Rewrite using `[ψ.left_inv hyN.2, hsu _ hyN.2]`. Conclude with `congrArg (fun t => Real.log ‖u (c.symm y) * t‖) (hprod _)`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Rewrite using `[logNormSec_eq_indicator hS hp, hlog]`. Distinguish the cases in `h0 : s x0 (c.symm y) = 0`.

Rewrite using `[Set.indicator_of_mem (show y ∈ Z from ⟨hy, h0⟩), Set.indicator_of_mem (show c.symm y ∈ {q | s x0 q = 0} from h0)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.indicator_of_notMem (show y ∉ Z from fun h => h0 h.2), Set.indicator_of_notMem (show c.symm y ∉ {q | s x0 q = 0} from h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logNormIntegrable_of (hLU : ReciprocityTheory.AnForm.A.LogUnitMonoLocIntStatement)
    (hD : LocDensContStatement) : LogNormIntegrableStatement := by
  intro e X _ _ _ A L s r m W hL hS hSNC Φ hΦ j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y0 hy0 => ?_) hK
  set c := A.chart j with hc
  have hy0t : y0 ∈ c.target := hKt hy0
  obtain ⟨ψ, hψc, hx0ψ, hψU, σ, -, -, u, hu, hu0, hsu⟩ := hSNC (c.symm y0)
  set x0 := c.symm y0 with hx0
  have hNo : IsOpen (c.target ∩ c.symm ⁻¹' ψ.source) := c.isOpen_inter_preimage_symm ψ.open_source
  have hy0N : y0 ∈ c.target ∩ c.symm ⁻¹' ψ.source := ⟨hy0t, hx0ψ⟩
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.mp hNo y0 hy0N
  set B := Metric.closedBall y0 (ε / 2) with hB
  have hBN : B ⊆ c.target ∩ c.symm ⁻¹' ψ.source :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεN
  have hBc : IsCompact B := isCompact_closedBall y0 (ε / 2)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩

  set V := ψ.target ∩ ψ.symm ⁻¹' c.source with hV
  have hVo : IsOpen V := ψ.isOpen_inter_preimage_symm c.open_source
  have hTinvA : AnalyticOnNhd ℂ (c ∘ ψ.symm) V := (hψc j).2
  have hTV : ∀ y ∈ c.target ∩ c.symm ⁻¹' ψ.source,
      ψ (c.symm y) ∈ V ∧ c (ψ.symm (ψ (c.symm y))) = y := by
    intro y hy
    refine ⟨⟨ψ.map_source hy.2, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, ψ.left_inv hy.2]
      exact c.map_target hy.1
    · rw [ψ.left_inv hy.2, c.right_inv hy.1]

  set m' : Fin e → ℤ :=
    fun i => ((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ) : ℤ) with hm'
  set G : (Fin e → ℂ) → ℝ := fun z => Real.log ‖u (ψ.symm z) * ∏ i, z i ^ m' i‖ with hG
  have hGloc : LocallyIntegrableOn G V := by
    refine hLU e m' V (fun z => u (ψ.symm z)) hVo ?_ (fun z hz => hu0 _ (ψ.map_target hz.1))
    intro z hz
    have hw : c (ψ.symm z) ∈ c.target ∩ c.symm ⁻¹' ψ.source := by
      refine ⟨c.map_source hz.2, ?_⟩
      simp only [Set.mem_preimage, c.left_inv hz.2]
      exact ψ.map_target hz.1
    have h1 : AnalyticAt ℂ ((u ∘ c.symm) ∘ (c ∘ ψ.symm)) z :=
      AnalyticAt.comp (g := u ∘ c.symm) (f := c ∘ ψ.symm) (hu j _ hw) (hTinvA z hz)
    refine (h1.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVo.mem_nhds hz] with w hw
    simp [Function.comp, c.left_inv hw.2]

  have hTc : ContinuousOn (fun y => ψ (c.symm y)) (c.target ∩ c.symm ⁻¹' ψ.source) :=
    ψ.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left) (fun y hy => hy.2)
  set C := (fun y => ψ (c.symm y)) '' B with hC
  have hCc : IsCompact C := hBc.image_of_continuousOn (hTc.mono hBN)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hCV : C ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hTV y (hBN hy)).1
  have hCB : (c ∘ ψ.symm) '' C = B := by
    rw [hC, Set.image_image]
    conv_rhs => rw [← Set.image_id B]
    exact Set.image_congr fun y hy => (hTV y (hBN hy)).2
  have hinj : Set.InjOn (c ∘ ψ.symm) C := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    simp only [Function.comp_apply] at h
    rw [(hTV y (hBN hy)).2, (hTV y' (hBN hy')).2] at h
    rw [h]
  have hderR : ∀ z ∈ V, DifferentiableAt ℝ (c ∘ ψ.symm) z := fun z hz =>
    (hTinvA z hz).differentiableAt.restrictScalars ℝ
  have hdetc : ContinuousOn (fun z => |(fderiv ℝ (c ∘ ψ.symm) z).det|) C := by
    have h1 : ContDiffOn ℝ 1 (c ∘ ψ.symm) V :=
      (hTinvA.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ
    exact ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (h1.continuousOn_fderiv_of_isOpen hVo le_rfl)).abs).mono hCV
  have hGT : IntegrableOn (fun y => G (ψ (c.symm y))) B := by
    have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      hCm (f := c ∘ ψ.symm) (f' := fun z => fderiv ℝ (c ∘ ψ.symm) z)
      (fun z hz => (hderR z (hCV hz)).hasFDerivAt.hasFDerivWithinAt) hinj
      (fun y => G (ψ (c.symm y)))
    rw [hCB] at hiff
    refine hiff.mpr ?_
    refine IntegrableOn.congr_fun
      ((hGloc.integrableOn_compact_subset hCV hCc).continuousOn_smul hdetc hCc) ?_ hCm
    rintro _ ⟨y, hy, rfl⟩
    have h := (hTV y (hBN hy)).2
    simp only [Function.comp_apply, h]

  have hdB : ContinuousOn (locDens A Φ j) B :=
    (hD A Φ hΦ j).mono (hBN.trans Set.inter_subset_left)
  have hsub : c.target ∩ c.symm ⁻¹' ψ.source ⊆ c.target ∩ c.symm ⁻¹' L.U x0 :=
    fun y hy => ⟨hy.1, hψU hy.2⟩
  have hφB : ContinuousOn (fun y => L.φ x0 (c.symm y)) B :=
    ((hL.1 x0 j).continuousOn.mono hsub).mono hBN
  have hsB : ContinuousOn (fun y => s x0 (c.symm y)) B :=
    ((hS.1 x0 j).continuousOn.mono hsub).mono hBN
  set Z := B ∩ (fun y => s x0 (c.symm y)) ⁻¹' {0} with hZ
  have hZm : MeasurableSet Z :=
    (hsB.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton).measurableSet
  have h1 : IntegrableOn (fun y => G (ψ (c.symm y)) * locDens A Φ j y) B :=
    hGT.mul_continuousOn hdB hBc
  have h2 : IntegrableOn (fun y => L.φ x0 (c.symm y) * locDens A Φ j y) B :=
    (hφB.mul hdB).integrableOn_compact hBc
  have h3 := h2.indicator hZm
  refine IntegrableOn.congr_fun (Integrable.add (Integrable.sub h1 h2) h3) ?_ hBm
  intro y hy
  have hyN := hBN hy
  have hp : c.symm y ∈ L.U x0 := hψU hyN.2
  have hprod : ∀ w : Fin e → ℂ, (∏ k, (match σ k with
      | some i => w i ^ m k
      | none => 1)) = ∏ i, w i ^ m' i := by
    intro w
    apply prod_option_eq_prod_zpow
    intro k
    split <;> simp_all
  have hlog : Real.log ‖s x0 (c.symm y)‖ = G (ψ (c.symm y)) := by
    show _ = Real.log ‖u (ψ.symm (ψ (c.symm y))) * ∏ i, (ψ (c.symm y)) i ^ m' i‖
    rw [ψ.left_inv hyN.2, hsu _ hyN.2]
    exact congrArg (fun t => Real.log ‖u (c.symm y) * t‖) (hprod _)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [logNormSec_eq_indicator hS hp, hlog]
  by_cases h0 : s x0 (c.symm y) = 0
  · rw [Set.indicator_of_mem (show y ∈ Z from ⟨hy, h0⟩),
      Set.indicator_of_mem (show c.symm y ∈ {q | s x0 q = 0} from h0)]
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Z from fun h => h0 h.2),
      Set.indicator_of_notMem (show c.symm y ∉ {q | s x0 q = 0} from h0)]
    ring

/- English proof (translation)
The claim follows from `logNormIntegrable_of ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm locDensCont`.
-/
theorem logNormIntegrable : LogNormIntegrableStatement :=
  logNormIntegrable_of ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm locDensCont

end

end ReciprocityTheory.AnForm.M
