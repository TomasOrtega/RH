import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
/- English proof (translation)
Establish `h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v` using `Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ`. Establish `hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v` using `(h.fderiv_right (m := 0) (by norm_num)).continuousAt`. Simplify using `only [_root_.GlobalTheory.dbar_apply]`. Use `fun_prop`.
-/
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
/- English proof (translation)
The claim follows from `Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)`.
-/
private lemma le_fintype_sum_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

/- English proof (translation)
Introduce `n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ`. Set `F : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ` to `fun v => |ρ v| + ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ + ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ + ∑ a, ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv …`. Establish `hFc : ContinuousOn F K`. Introduce `v hv`. Establish `hvU : v ∈ U` using `hKU hv`.

Establish `hρv : ContDiffAt ℝ ∞ ρ v` using `hρ.contDiffAt (hU.mem_nhds hvU)`. Establish `h1 : ContinuousAt ρ v` using `hρv.continuousAt`. Establish `h2 : ∀ b, ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x (_root_.GlobalTheory.GoodMetric.coordVec b)) v` using `fun b => continuousAt_dbar_ofReal_of_contDiffAt_one (hρv.of_le (by simp)) _`. Establish `h3 : ∀ a i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.conn G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) i j) v` using `fun a i j => ((hG₀ v hvU).1.conn (j := 0) (hG₀ v hvU).2 (by simp) (_root_.GlobalTheory.GoodMetric.coordVec a) i j).continuousAt`. Establish `h4 : ∀ a b i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j) v` using `fun a b i j => ((hG₀ v hvU).1.curv (j := 0) (hG₀ v hvU).2 (by rw [zero_add]; exact WithTop.coe_le_coe.2 le_top) (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j).continuousAt`.

Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Simplify using `only [F]`. Use `fun_prop`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hFc`. Use `⟨max C 0, le_max_right _ _, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `hFv : F v ≤ max C 0` using `((le_abs_self _).trans (hC v hv)).trans (le_max_left _ _)`. Establish `hA : 0 ≤ |ρ v|` using `abs_nonneg _`. Establish `hB : 0 ≤ ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hC3 : 0 ≤ ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hD : 0 ≤ ∑ a, ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.

Simplify using `only [F] at hFv`. Use `⟨by linarith, fun b => ?_, fun a i j => ?_, fun a b i j => ?_⟩` and prove the remaining obligations. Use `le_fintype_sum_of_nonneg (fun b => ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖) (fun _ => norm_nonneg _) b` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `le_fintype_sum_of_nonneg (fun j => ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖) (fun _ => norm_nonneg _) j`.

Establish `e2` using `le_fintype_sum_of_nonneg (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖) (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i`. Establish `e3` using `le_fintype_sum_of_nonneg (fun a => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖) (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) a`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `le_fintype_sum_of_nonneg (fun j => ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖) (fun _ => norm_nonneg _) j`. Establish `e2` using `le_fintype_sum_of_nonneg (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖) (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i`.

Establish `e3` using `le_fintype_sum_of_nonneg (fun b => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖) (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) b`. Establish `e4` using `le_fintype_sum_of_nonneg (fun a => ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖) (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ = …`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.GoodTop.exists_bound_smooth_data : ∀ {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) →
    ContDiffOn ℝ ∞ ρ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ K, |ρ v| ≤ C ∧
      (∀ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ ≤ C) ∧
      (∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ ≤ C) ∧
      ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ ≤ C := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ
  let F : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => |ρ v|
    + ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖
    + ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖
    + ∑ a, ∑ b, ∑ i, ∑ j,
        ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖
  have hFc : ContinuousOn F K := by
    intro v hv
    have hvU : v ∈ U := hKU hv
    have hρv : ContDiffAt ℝ ∞ ρ v := hρ.contDiffAt (hU.mem_nhds hvU)
    have h1 : ContinuousAt ρ v := hρv.continuousAt
    have h2 : ∀ b, ContinuousAt
        (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x (_root_.GlobalTheory.GoodMetric.coordVec b)) v :=
      fun b => continuousAt_dbar_ofReal_of_contDiffAt_one (hρv.of_le (by simp)) _
    have h3 : ∀ a i j, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G₀ x (_root_.GlobalTheory.GoodMetric.coordVec a) i j) v := fun a i j =>
      ((hG₀ v hvU).1.conn (j := 0) (hG₀ v hvU).2 (by simp)
        (_root_.GlobalTheory.GoodMetric.coordVec a) i j).continuousAt
    have h4 : ∀ a b i j, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G₀ x
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j) v :=
      fun a b i j =>
      ((hG₀ v hvU).1.curv (j := 0) (hG₀ v hvU).2
        (by rw [zero_add]; exact WithTop.coe_le_coe.2 le_top)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j).continuousAt
    apply ContinuousAt.continuousWithinAt
    simp only [F]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hFc
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  have hFv : F v ≤ max C 0 := ((le_abs_self _).trans (hC v hv)).trans (le_max_left _ _)
  have hA : 0 ≤ |ρ v| := abs_nonneg _
  have hB : 0 ≤ ∑ b, ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v
      (_root_.GlobalTheory.GoodMetric.coordVec b)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC3 : 0 ≤ ∑ a, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  have hD : 0 ≤ ∑ a, ∑ b, ∑ i, ∑ j,
      ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [F] at hFv
  refine ⟨by linarith, fun b => ?_, fun a i j => ?_, fun a b i j => ?_⟩
  · have := le_fintype_sum_of_nonneg
      (fun b => ‖_root_.GlobalTheory.dbar (fun x => (ρ x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖)
      (fun _ => norm_nonneg _) b
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun a => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.conn G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith
  · have e1 := le_fintype_sum_of_nonneg
      (fun j => ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => norm_nonneg _) j
    have e2 := le_fintype_sum_of_nonneg
      (fun i => ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) i
    have e3 := le_fintype_sum_of_nonneg
      (fun b => ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) b
    have e4 := le_fintype_sum_of_nonneg
      (fun a => ∑ b, ∑ i, ∑ j, ‖_root_.GlobalTheory.HermFrame.curv G₀ v (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖)
      (fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _) a
    linarith

end GlobalTheory.GoodTop
