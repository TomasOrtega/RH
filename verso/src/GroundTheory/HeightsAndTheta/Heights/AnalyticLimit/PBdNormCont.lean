import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

/- English proof (translation)
Introduce `X _ D A R φ hφ c`. Use `continuous_iff_continuousAt.2 fun y₀ => ?_` and prove the remaining obligations. Use `set j := bdIdx R y₀`. Establish `hU : IsOpen (bdDom R j)` using `isOpen_bdDom R j`. Establish `hy₀ : y₀ ∈ bdDom R j` using `mem_bdDom_bdIdx R y₀`.

Establish `hEqc : ContinuousOn (bdEq R j) (bdDom R j)` using `(hCC D A _ hU).2 _ (hEq D A R j).1`. Establish `hφc : ContinuousOn (φ j) (bdDom R j)` using `(hCC D A _ hU).1 _ (hφ.1 j)`. Establish `hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j)` using `hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)`. Establish `hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀` using `hg.continuousAt (hU.mem_nhds hy₀)`. Use `hgy.congr ?_` and prove the remaining obligations.

Use `filter_upwards [hU.mem_nhds hy₀] with y hy`. Establish `hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j` using `⟨mem_bdDom_bdIdx R y, hy⟩`. Establish `h3` using `hφ.2.2 (bdIdx R y) j y hk`. Use `show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)`. Simplify using `only [bdSec, bdPot]`.

Simplify using `only [neg_add, Real.exp_add, ← mul_assoc, h3]`.
-/
theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
