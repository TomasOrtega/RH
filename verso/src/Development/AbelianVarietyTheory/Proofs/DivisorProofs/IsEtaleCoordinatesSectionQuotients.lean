import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

section QuotEtale

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {B : La} {t0 : ι → Y → ℂ} {t : Fin n → ι → Y → ℂ}

end QuotEtale

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] in
/- English proof (translation)
Establish `h` using `hs`. Unfold `_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h`. Conclude with `h.2 i j y (Set.mem_univ y) hi hj`.
-/
private lemma sec_eq_transition_mul {A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La} {B : La} {s : ι → Y → ℂ}
    (hs : A.IsSec B s) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : s i y = A.g B i j y * s j y := by
  have h := hs
  unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h
  exact h.2 i j y (Set.mem_univ y) hi hj

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord`. Establish `hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0`. Introduce `i y hy hi`. Rewrite using `[sec_eq_transition_mul h0 hi (A.mem_pick y)]`. Conclude with `mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1`.

Establish `hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → A.zmap t0 t y = A.zLoc t0 t i (A.chart i y)`. Introduce `i y hy hi`. Unfold `_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc`. Rewrite using `[(A.chart i).left_inv hi]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[sec_eq_transition_mul (ht k) hi (A.mem_pick y), sec_eq_transition_mul h0 hi (A.mem_pick y)]`. Conclude with `(mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm`. Establish `hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)`. Introduce `i`.

Apply `(differentiableOn_piLp (𝕜 := ℂ) 2).2` to reduce the goal to its premises. Introduce `k`. Establish `hk` using `ht k`. Establish `h0'` using `h0`. Unfold `_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'`.

Establish `hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ` using `fun v hv => ⟨hv.1, Set.mem_univ _⟩`. Establish `hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v)) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(hk.1 i).mono hsub`. Establish `hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v)) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(h0'.1 i).mono hsub`. Establish `hdiv : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v)) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)`. Simplify using `only [div_eq_mul_inv]`.

Conclude with `hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))`. Unfold `_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc`. Conclude with `hdiv`. Use `⟨hU, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `(hloc i).congr ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]`. Introduce `i y hy hi`.

Unfold `_root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz`. Use `set j := A.pick y with hj_def`. Establish `hj : y ∈ (A.chart j).source` using `A.mem_pick y`. Establish `hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈ 𝓝 (A.chart i y)`. Use `((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_` and prove the remaining obligations.

Use `⟨(A.chart i).map_source hi, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, (A.chart i).left_inv hi]`. Conclude with `⟨hy, hj⟩`. Establish `heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)] A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm)` using `by filter_upwards [hV] with v hv`. Simplify using `only [Function.comp_apply]`.

Conclude with `hz j _ hv.2.1 hv.2.2`. Rewrite using `[heq.fderiv_eq]`. Establish `hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)`. Use `(A.holo_trans i j).differentiableAt ?_` and prove the remaining obligations. Establish `ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source)` using `(A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source`.

Use `ho.mem_nhds ?_` and prove the remaining obligations. Use `⟨(A.chart i).map_source hi, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, (A.chart i).left_inv hi]`. Conclude with `hj`. Establish `hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y`.

Simplify using `only [Function.comp_apply, (A.chart i).left_inv hi]`. Establish `hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y))`. Rewrite using `[hTy]`. Use `(hloc j).differentiableAt ?_` and prove the remaining obligations. Use `((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_` and prove the remaining obligations.

Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, (A.chart j).left_inv hj]`. Conclude with `hy`. Rewrite using `[fderiv_comp _ hL hT, hTy]`. Establish `hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _ …` using `LinearMap.det_comp _ _`.

Rewrite using `[ContinuousLinearMap.det, hdet]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Establish `hc` using `(hcoord y hy).2`. Unfold `_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc`. Conclude with `hc`.

Establish `hk` using `A.g_kap i j y hi hj`. Establish `hg` using `A.g_ne A.kap i j y hi hj`. Rewrite `hg` using `[hk]`. Conclude with `hg`.
-/
theorem _root_.GlobalTheory.OTY.etale_zmap_main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y),
    A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U →
    (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → _root_.GlobalTheory.OTY.Etale A U (A.zmap t0 t) := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord
  have hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0 := by
    intro i y hy hi
    rw [sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1
  have hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source →
      A.zmap t0 t y = A.zLoc t0 t i (A.chart i y) := by
    intro i y hy hi
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    rw [(A.chart i).left_inv hi]
    congr 1
    funext k
    rw [sec_eq_transition_mul (ht k) hi (A.mem_pick y),
      sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact (mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm
  have hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
    intro i
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).2
    intro k
    have hk := ht k
    have h0' := h0
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, Set.mem_univ _⟩
    have hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hk.1 i).mono hsub
    have hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (h0'.1 i).mono hsub
    have hdiv : DifferentiableOn ℂ
        (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
      simp only [div_eq_mul_inv]
      exact hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    exact hdiv
  refine ⟨hU, ?_, ?_⟩
  · intro i
    refine (hloc i).congr ?_
    intro v hv
    simp only [Function.comp_apply]
    rw [hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]
  · intro i y hy hi
    unfold _root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz
    set j := A.pick y with hj_def
    have hj : y ∈ (A.chart j).source := A.mem_pick y
    have hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈
        𝓝 (A.chart i y) := by
      refine ((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact ⟨hy, hj⟩
    have heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm) := by
      filter_upwards [hV] with v hv
      simp only [Function.comp_apply]
      exact hz j _ hv.2.1 hv.2.2
    rw [heq.fderiv_eq]
    have hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) := by
      refine (A.holo_trans i j).differentiableAt ?_
      have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
      refine ho.mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact hj
    have hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
    have hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hTy]
      refine (hloc j).differentiableAt ?_
      refine ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_
      refine ⟨(A.chart j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]
      exact hy
    rw [fderiv_comp _ hL hT, hTy]
    have hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp
        (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :
          _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) =
        LinearMap.det (fderiv ℂ (A.zLoc t0 t j) (A.chart j y) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) *
          LinearMap.det (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) :
            _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :=
      LinearMap.det_comp _ _
    rw [ContinuousLinearMap.det, hdet]
    refine mul_ne_zero ?_ ?_
    · have hc := (hcoord y hy).2
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc
      exact hc
    · have hk := A.g_kap i j y hi hj
      have hg := A.g_ne A.kap i j y hi hj
      rw [hk] at hg
      exact hg

end GlobalTheory.OTY
