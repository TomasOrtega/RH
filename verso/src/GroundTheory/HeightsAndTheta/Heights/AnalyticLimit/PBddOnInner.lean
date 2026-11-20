import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

/- English proof (translation)
Establish `hW : closure (R.W'' j) ⊆ R.W j` using `(R.closure_W''_subset j).trans (subset_closure.trans (R.closure_W'_subset j))`. Establish `hT : closure (R.W'' j) ⊆ (R.ψ j).target` using `hW.trans (R.W_subset j)`. Establish `hc : IsCompact (closure (R.W'' j))` using `(R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure ((R.closure_W''_subset j).trans subset_closure)`. Use `⟨hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hT), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Use `⟨(R.ψ j).map_target (hT hz), ?_⟩` and prove the remaining obligations. Use `show R.ψ j ((R.ψ j).symm z) ∈ R.W j`. Rewrite using `[(R.ψ j).right_inv (hT hz)]`. Conclude with `hW hz`. Introduce `y hy`.

Conclude with `⟨R.ψ j y, subset_closure hy.2, (R.ψ j).left_inv hy.1⟩`.
-/
theorem bdDom_compact_inner {D : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (j : Fin R.n) :
    IsCompact ((R.ψ j).symm '' closure (R.W'' j)) ∧
      (R.ψ j).symm '' closure (R.W'' j) ⊆ bdDom R j ∧
      R.V'' j ⊆ (R.ψ j).symm '' closure (R.W'' j) := by
  have hW : closure (R.W'' j) ⊆ R.W j :=
    (R.closure_W''_subset j).trans (subset_closure.trans (R.closure_W'_subset j))
  have hT : closure (R.W'' j) ⊆ (R.ψ j).target := hW.trans (R.W_subset j)
  have hc : IsCompact (closure (R.W'' j)) :=
    (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
      ((R.closure_W''_subset j).trans subset_closure)
  refine ⟨hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hT), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(R.ψ j).map_target (hT hz), ?_⟩
    show R.ψ j ((R.ψ j).symm z) ∈ R.W j
    rw [(R.ψ j).right_inv (hT hz)]
    exact hW hz
  · intro y hy
    exact ⟨R.ψ j y, subset_closure hy.2, (R.ψ j).left_inv hy.1⟩

/- English proof (translation)
Introduce `X _ D A R j u hu`. Take `⟨hK, hKD, hVK⟩` from `bdDom_compact_inner R j`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn (hu.mono hKD)`. Conclude with `⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y (hVK hy)⟩`.
-/
theorem BddOnInner.proof : BddOnInner.Statement := by
  intro X _ D A R j u hu
  obtain ⟨hK, hKD, hVK⟩ := bdDom_compact_inner R j
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hu.mono hKD)
  exact ⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y (hVK hy)⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
