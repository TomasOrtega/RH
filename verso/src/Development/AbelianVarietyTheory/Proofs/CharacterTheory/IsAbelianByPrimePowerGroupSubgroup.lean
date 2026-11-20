import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
namespace GlobalTheory.BI

/- English proof (translation)
Introduce `G _ T h`. Unfold `_root_.GlobalTheory.BI.AbByP at h ⊢`. Take `⟨p, hp, A, hA, hcomm, hpow⟩` from `h`. Use `haveI := hA`. Use `⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a ha b hb`. Conclude with `Subtype.ext (hcomm _ ha _ hb)`. Introduce `g`. Take `⟨n, hn⟩` from `hpow g`. Conclude with `⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩`.
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
