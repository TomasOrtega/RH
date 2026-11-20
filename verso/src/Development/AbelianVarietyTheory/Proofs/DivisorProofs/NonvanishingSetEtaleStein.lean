import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIffStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[A.nsq_eq_chart hs hy]`. Establish `h1 : ‖τ i y‖ ^ 2 ≠ 0` using `by positivity`. Rewrite using `[Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, norm_inv, inv_pow, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nzStein_germ {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    -Real.log (A.nsq Λ τ y) = (A.ph Λ i y + 0) + Real.log (‖(τ i y)⁻¹‖ ^ 2) := by
  rw [A.nsq_eq_chart hs hy]
  have h1 : ‖τ i y‖ ^ 2 ≠ 0 := by positivity
  rw [Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, norm_inv, inv_pow, Real.log_inv]
  ring

/- English proof (translation)
Establish `hT : (A.chart i).target ∈ 𝓝 (A.chart i y)` using `(A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)`. Establish `hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target`. Simplify `hs.1 i` using `[WeightedAtlas.IsSec, WeightedAtlas.IsSecOn]`. Establish `hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y)`. Establish `h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y)` using `(ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT`.

Conclude with `h.restrict_scalars ℝ`. Establish `hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0`. Simplify `hτ` using `[(A.chart i).left_inv hy]`. Establish `hlog` using `((hτc.inv hne).norm_sq ℝ).log (by simpa using hne)`. Simplify `hlog` using `[Function.comp_def]`.
-/
theorem nzStein_smoothLog {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) := by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hlog := ((hτc.inv hne).norm_sq ℝ).log (by simpa using hne)
  simpa [Function.comp_def] using hlog

/- English proof (translation)
Establish `hT : (A.chart i).target ∈ 𝓝 (A.chart i y)` using `(A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)`. Establish `hph : ContDiffAt ℝ ∞ (A.ph Λ i ∘ (A.chart i).symm) (A.chart i y)` using `(A.smooth_ph Λ i).contDiffAt hT`. Establish `hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target`. Simplify `hs.1 i` using `[WeightedAtlas.IsSec, WeightedAtlas.IsSecOn]`. Establish `hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y)`.

Establish `h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y)` using `(ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT`. Conclude with `h.restrict_scalars ℝ`. Establish `hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0`. Simplify `hτ` using `[(A.chart i).left_inv hy]`. Establish `hinv : ContDiffAt ℝ ∞ (fun v => ((τ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i y)` using `hτc.inv hne`.

Establish `hsq : ContDiffAt ℝ ∞ (fun v => ‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2) (A.chart i y)` using `hinv.norm_sq ℝ`. Establish `hlog : ContDiffAt ℝ ∞ (fun v => Real.log (‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2)) (A.chart i y)` using `hsq.log (by simpa using hne)`. Conclude with `(hph.add contDiffAt_const).add (by simpa [Function.comp_def] using hlog)`.
-/
theorem nzStein_smooth {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => (A.ph Λ i x + 0) + Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hph : ContDiffAt ℝ ∞ (A.ph Λ i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph Λ i).contDiffAt hT
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
    by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hinv : ContDiffAt ℝ ∞ (fun v => ((τ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i y) :=
    hτc.inv hne
  have hsq : ContDiffAt ℝ ∞ (fun v => ‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2) (A.chart i y) :=
    hinv.norm_sq ℝ
  have hlog : ContDiffAt ℝ ∞ (fun v => Real.log (‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2))
      (A.chart i y) :=
    hsq.log (by simpa using hne)
  exact (hph.add contDiffAt_const).add (by simpa [Function.comp_def] using hlog)

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `n Y _ _ _ _ _ _ ι La _ A Λ τ z hs hpos hE`. Establish `hW : ∀ x ∈ nz A τ, ∀ᶠ y in 𝓝 x, (fun y => -Real.log (A.nsq Λ τ y)) y = (fun y => (A.ph Λ (A.pick x) y + 0) + Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) y`. Introduce `x hx`. Establish `hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ)` using `(A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source isOpen_compl_singleton`. Use `filter_upwards [hO.mem_nhds ⟨A.mem_pick x, hx⟩] with y hy`.

Conclude with `nzStein_germ A hs (A.pick x) hy.1 hy.2`. Establish `hT : ∀ x, Tendsto (A.chart (A.pick x)).symm (𝓝 (A.chart (A.pick x) x)) (𝓝 x)`. Introduce `x`. Use `(A.chart (A.pick x)).continuousAt_symm ((A.chart (A.pick x)).map_source (A.mem_pick x))` as an intermediate fact. Rewrite `this` using `[ContinuousAt, (A.chart (A.pick x)).left_inv (A.mem_pick x)]`. Then use the resulting hypothesis.

Establish `hsm : ∀ x ∈ nz A τ, ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq Λ τ y)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x)`. Introduce `x hx`. Use `(nzStein_smooth A hs (A.pick x) (A.mem_pick x) hx).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(hT x).eventually (hW x hx)] with v hv`. Conclude with `hv`.

Establish `hlev : ∀ x ∈ nz A τ, ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt (A.pick x) (fun y => -Real.log (A.nsq Λ τ y)) x ξ`. Introduce `x hx ξ`. Establish `hxi : x ∈ (A.chart (A.pick x)).source` using `A.mem_pick x`. Rewrite using `[leviAt_congr A (A.pick x) _ _ x hxi (hW x hx) ξ]`. Establish `hT' : (A.chart (A.pick x)).target ∈ 𝓝 (A.chart (A.pick x) x)` using `(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi)`.

Establish `hf : ContDiffAt ℝ 2 ((fun y => A.ph Λ (A.pick x) y + 0) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x)`. Establish `: ContDiffAt ℝ ∞ (A.ph Λ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x)` using `(A.smooth_ph Λ (A.pick x)).contDiffAt hT'`. Conclude with `(this.add contDiffAt_const).of_le (WithTop.coe_le_coe.mpr le_top)`. Establish `hg : ContDiffAt ℝ 2 ((fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x)` using `(nzStein_smoothLog A hs (A.pick x) hxi hx).of_le (WithTop.coe_le_coe.mpr le_top)`. Establish `hd : DifferentiableOn ℂ (τ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x)).target`.

Simplify `hs.1 (A.pick x)` using `[WeightedAtlas.IsSec, WeightedAtlas.IsSecOn]`. Establish `hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ)` using `(A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source isOpen_compl_singleton`. Establish `hh : ∀ᶠ v in 𝓝 (A.chart (A.pick x) x), DifferentiableAt ℂ ((fun y => (τ (A.pick x) y)⁻¹) ∘ (A.chart (A.pick x)).symm) v` using `by filter_upwards [(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi), (hT x).eventually (hO.mem_nhds ⟨hxi, hx⟩)] with v hv1 hv2`. Conclude with `(hd.differentiableAt ((A.chart (A.pick x)).open_target.mem_nhds hv1)).inv hv2.2`. Establish `E1` using `leviAt_add A (A.pick x) (fun y => A.ph Λ (A.pick x) y + 0) (fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) x hf hg ξ`.

Establish `E2` using `leviAt_log_normSq A (A.pick x) (fun y => (τ (A.pick x) y)⁻¹) x hxi hh (inv_ne_zero hx) ξ`. Establish `hp` using `hpos (A.pick x) x hxi ξ`. Simplify using `only at E1 E2 hp`. Rewrite using `[E1, E2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hLH : IsLocalHomeomorph (fun y : nz A τ => z y)` using `GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A _ z hE`. Establish `hSm : SmoothR n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y))` using `(GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A _ z hE).2 (fun y => -Real.log (A.nsq Λ τ y)) (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx⟩)`. Establish `hLv : LeviNonneg n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y))` using `GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A _ z hE (fun y => -Real.log (A.nsq Λ τ y)) (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx, hlev x hx⟩)`. Establish `hC : ∀ a : ℝ, IsCompact {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a}`. Introduce `a`.

Establish `hK : IsCompact {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y}` using `(isClosed_le continuous_const (A.continuous_nsq hs)).isCompact`. Establish `hsub : {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} ⊆ nz A τ`. Introduce `y hy`. Use `show τ (A.pick y) y ≠ 0`. Introduce `h0`.

Establish `h1 : Real.exp (-a) ≤ A.nsq Λ τ y` using `hy`. Establish `h2 : A.nsq Λ τ y = 0` using `by simp [WeightedAtlas.nsq, h0]`. Use `Real.exp_pos (-a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heq : {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} = Subtype.val ⁻¹' {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y}`.

Use extensionality with `⟨y, hy⟩`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`. Establish `hne : τ (A.pick y) y ≠ 0` using `hy`. Establish `hp : 0 < A.nsq Λ τ y`. Unfold `WeightedAtlas.nsq`.

Check the signs of the components of the expression. Rewrite using `[neg_le, Real.le_log_iff_exp_le hp]`. Rewrite using `[heq, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub)]`. Conclude with `hK`. Conclude with `⟨⟨fun y => z y, hLH, fun y => -Real.log (A.nsq Λ τ y), hSm, hLv, hC⟩, rfl, rfl⟩`.
-/
theorem nzEtaleStein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  intro n Y _ _ _ _ _ _ ι La _ A Λ τ z hs hpos hE

  have hW : ∀ x ∈ nz A τ, ∀ᶠ y in 𝓝 x, (fun y => -Real.log (A.nsq Λ τ y)) y =
      (fun y => (A.ph Λ (A.pick x) y + 0) + Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) y := by
    intro x hx
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    filter_upwards [hO.mem_nhds ⟨A.mem_pick x, hx⟩] with y hy
    exact nzStein_germ A hs (A.pick x) hy.1 hy.2
  have hT : ∀ x, Tendsto (A.chart (A.pick x)).symm (𝓝 (A.chart (A.pick x) x)) (𝓝 x) := by
    intro x
    have := (A.chart (A.pick x)).continuousAt_symm ((A.chart (A.pick x)).map_source (A.mem_pick x))
    rwa [ContinuousAt, (A.chart (A.pick x)).left_inv (A.mem_pick x)] at this
  have hsm : ∀ x ∈ nz A τ, ContDiffAt ℝ ∞
      ((fun y => -Real.log (A.nsq Λ τ y)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) := by
    intro x hx
    refine (nzStein_smooth A hs (A.pick x) (A.mem_pick x) hx).congr_of_eventuallyEq ?_
    filter_upwards [(hT x).eventually (hW x hx)] with v hv
    exact hv
  have hlev : ∀ x ∈ nz A τ, ∀ ξ : Fin n → ℂ,
      0 ≤ A.leviAt (A.pick x) (fun y => -Real.log (A.nsq Λ τ y)) x ξ := by
    intro x hx ξ
    have hxi : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
    rw [leviAt_congr A (A.pick x) _ _ x hxi (hW x hx) ξ]
    have hT' : (A.chart (A.pick x)).target ∈ 𝓝 (A.chart (A.pick x) x) :=
      (A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi)
    have hf : ContDiffAt ℝ 2 ((fun y => A.ph Λ (A.pick x) y + 0) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) := by
      have : ContDiffAt ℝ ∞ (A.ph Λ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) :=
        (A.smooth_ph Λ (A.pick x)).contDiffAt hT'
      exact (this.add contDiffAt_const).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg : ContDiffAt ℝ 2
        ((fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      (nzStein_smoothLog A hs (A.pick x) hxi hx).of_le (WithTop.coe_le_coe.mpr le_top)
    have hd : DifferentiableOn ℂ (τ (A.pick x) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x)).target := by
      simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 (A.pick x)
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    have hh : ∀ᶠ v in 𝓝 (A.chart (A.pick x) x),
        DifferentiableAt ℂ ((fun y => (τ (A.pick x) y)⁻¹) ∘ (A.chart (A.pick x)).symm) v := by
      filter_upwards [(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi),
        (hT x).eventually (hO.mem_nhds ⟨hxi, hx⟩)] with v hv1 hv2
      exact (hd.differentiableAt ((A.chart (A.pick x)).open_target.mem_nhds hv1)).inv hv2.2
    have E1 := leviAt_add A (A.pick x) (fun y => A.ph Λ (A.pick x) y + 0)
      (fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) x hf hg ξ
    have E2 := leviAt_log_normSq A (A.pick x) (fun y => (τ (A.pick x) y)⁻¹) x hxi hh (inv_ne_zero hx) ξ
    have hp := hpos (A.pick x) x hxi ξ
    simp only at E1 E2 hp
    rw [E1, E2]
    linarith
  have hLH : IsLocalHomeomorph (fun y : nz A τ => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A _ z hE
  have hSm : SmoothR n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A _ z hE).2 (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx⟩)
  have hLv : LeviNonneg n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A _ z hE (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx, hlev x hx⟩)
  have hC : ∀ a : ℝ, IsCompact {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} := by
    intro a
    have hK : IsCompact {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} :=
      (isClosed_le continuous_const (A.continuous_nsq hs)).isCompact
    have hsub : {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} ⊆ nz A τ := by
      intro y hy
      show τ (A.pick y) y ≠ 0
      intro h0
      have h1 : Real.exp (-a) ≤ A.nsq Λ τ y := hy
      have h2 : A.nsq Λ τ y = 0 := by simp [WeightedAtlas.nsq, h0]
      have := Real.exp_pos (-a)
      linarith
    have heq : {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} =
        Subtype.val ⁻¹' {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      have hne : τ (A.pick y) y ≠ 0 := hy
      have hp : 0 < A.nsq Λ τ y := by
        unfold WeightedAtlas.nsq
        positivity
      rw [neg_le, Real.le_log_iff_exp_le hp]
    rw [heq, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub)]
    exact hK
  exact ⟨⟨fun y => z y, hLH, fun y => -Real.log (A.nsq Λ τ y), hSm, hLv, hC⟩, rfl, rfl⟩

end GlobalTheory
