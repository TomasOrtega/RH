import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesIsLattice

/- English proof (translation)
Rewrite using `[← (integralBasis K).sum_repr t, Finset.sum_smul]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, integralBasis_apply, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))`.
-/
theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact smul_mem_span_of_mem M t hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul q x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ q hx`.
-/
theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx

def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv

end KLinesIsLattice

/- English proof (translation)
Introduce `K _ _ ι _ M hfg hspan`. Use `⟨hfg, ?_⟩` and prove the remaining obligations. Establish `hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M` using `Submodule.span_le.mpr fun v hv => Submodule.subset_span hv`. Rewrite `hMN` using `[hspan, top_le_iff]`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Establish `hv : v ∈ KLinesIsLattice.qSpan M` using `hMN ▸ Submodule.mem_top`. Conclude with `hv`.
-/
theorem LinesIsLattice.proof : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  refine ⟨hfg, ?_⟩
  have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
    Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
  rw [hspan, top_le_iff] at hMN
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
  exact hv

end GroundTheory.Heights₂.Heights
