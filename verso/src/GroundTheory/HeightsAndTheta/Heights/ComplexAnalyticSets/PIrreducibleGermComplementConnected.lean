import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
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
