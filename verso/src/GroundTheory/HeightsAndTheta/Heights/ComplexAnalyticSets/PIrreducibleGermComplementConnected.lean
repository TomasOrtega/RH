import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Introduce `σ _ X w h hX hirr hh hnot U hU`. Take `⟨N, hNo, hwN, hN⟩` from `hdense σ X w hX`. Establish `hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w` using `inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt`. Take `⟨B, hBo, hwB, hBU, hR⟩` from `hconn σ X w hX hirr _ hU'`. Establish `hBh : ∀ z ∈ B, AnalyticAt ℂ h z` using `fun z hz => (hBU hz).2`.

Establish `hcl : X ∩ B ⊆ closure (regLocus (X ∩ B))` using `hN B hBo fun z hz => (hBU hz).1.2`. Establish `hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0})`. Introduce and unpack `z ⟨hzXB, hz0⟩`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`.

Establish `hne : {y | h y ≠ 0} ∈ 𝓝 z` using `(hBh z hzXB.2).continuousAt.eventually_ne hz0`. Take `⟨y, ⟨hyt, hyh⟩, hyR⟩` from `mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)`. Conclude with `⟨y, hyt, hyR, hyh⟩`. Establish `hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Apply `hnot` to reduce the goal to its premises. Use `filter_upwards [hBo.mem_nhds hwB] with z hzB hzX`. Assume the negation of the conclusion as `hz0`. Take `⟨y, hyR, hyh⟩` from `closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩`.

Conclude with `hyh (hcon y hyR)`. Establish `hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0})` using `hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx) (fun x hx => hBh x (regLocus_subset _ hx).2) hex`. Conclude with `⟨B, hBo, hwB, fun z hz => (hBU hz).1.1, hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩`.
-/
theorem IrreducibleGermComplementConnected.proof (hdense : RegularLocusDense.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement)
    (hzeros : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermComplementConnected.Statement := by
  intro σ _ X w h hX hirr hh hnot U hU
  obtain ⟨N, hNo, hwN, hN⟩ := hdense σ X w hX
  have hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w :=
    inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt
  obtain ⟨B, hBo, hwB, hBU, hR⟩ := hconn σ X w hX hirr _ hU'
  have hBh : ∀ z ∈ B, AnalyticAt ℂ h z := fun z hz => (hBU hz).2
  have hcl : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hN B hBo fun z hz => (hBU hz).1.2

  have hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0}) := by
    rintro z ⟨hzXB, hz0⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hne : {y | h y ≠ 0} ∈ 𝓝 z := (hBh z hzXB.2).continuousAt.eventually_ne hz0
    obtain ⟨y, ⟨hyt, hyh⟩, hyR⟩ := mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)
    exact ⟨y, hyt, hyR, hyh⟩

  have hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    filter_upwards [hBo.mem_nhds hwB] with z hzB hzX
    by_contra hz0
    obtain ⟨y, hyR, hyh⟩ := closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩
    exact hyh (hcon y hyR)
  have hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0}) :=
    hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx)
      (fun x hx => hBh x (regLocus_subset _ hx).2) hex
  exact ⟨B, hBo, hwB, fun z hz => (hBU hz).1.1,
    hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
