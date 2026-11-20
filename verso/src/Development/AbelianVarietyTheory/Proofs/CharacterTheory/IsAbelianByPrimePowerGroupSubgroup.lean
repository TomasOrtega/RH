import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
namespace GlobalTheory.BI

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩

end GlobalTheory.BI
