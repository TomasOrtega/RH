import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
/- English proof (translation)
Unfold `_root_.GlobalTheory.GoodTop.offHyp`. Conclude with `Iff.rfl`.
-/
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

/- English proof (translation)
Use `ae_eq_set.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `measure_mono_null (fun v hv => (hv.2 (mem_offHyp_iff.1 hv.1).1).elim) measure_empty`. Use `measure_mono_null (t := ⋃ a ∈ (S : Set (Fin n)), {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0}) ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv.2 (mem_offHyp_iff.2 ⟨hv.1, h⟩)`. Use `(measure_biUnion_null_iff S.countable_toSet).2 fun a _ => ?_` and prove the remaining obligations. Set `L : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℝ] ℂ` to `(EuclideanSpace.proj a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ`.

Establish `hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0} = (LinearMap.ker L : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n))`. Use extensionality with `v`. Simplify using `[L]`. Rewrite using `[hset]`. Use `Measure.addHaar_submodule _ _ fun htop => ?_` and prove the remaining obligations.

Establish `hmem : EuclideanSpace.single a (1 : ℂ) ∈ LinearMap.ker L` using `htop ▸ Submodule.mem_top`. Simplify using `[L] at hmem`.
-/
lemma _root_.GlobalTheory.GoodTop.offHyp_ae_eq {n : ℕ} (S : Finset (Fin n))
    (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) : _root_.GlobalTheory.GoodTop.offHyp S U =ᵐ[volume] U := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · exact measure_mono_null
      (fun v hv => (hv.2 (mem_offHyp_iff.1 hv.1).1).elim) measure_empty
  · refine measure_mono_null (t := ⋃ a ∈ (S : Set (Fin n)), {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0})
      ?_ ?_
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
      by_contra h
      push_neg at h
      exact hv.2 (mem_offHyp_iff.2 ⟨hv.1, h⟩)
    · refine (measure_biUnion_null_iff S.countable_toSet).2 fun a _ => ?_
      let L : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℝ] ℂ :=
        (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ
      have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0} = (LinearMap.ker L : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) := by
        ext v
        simp [L]
      rw [hset]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have hmem : EuclideanSpace.single a (1 : ℂ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
      simp [L] at hmem

end GlobalTheory.GoodTop
