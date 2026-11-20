import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupInvMemStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n ψ hs ho`. Establish `hoc` using `GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs`. Establish `hnear` using `GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs`. Establish `hone : (1 : GL (Fin n) k) ∈ grp ψ`. Use `⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩` and prove the remaining obligations.

Establish `h0 : (1 : GL (Fin n) k).val i j = 0`. Simplify using `[Matrix.one_apply_ne (ne_of_lt hij)]`. Rewrite using `[h0]`. Conclude with `(GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _`. Use `⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1, GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩` and prove the remaining obligations.

Take `⟨U, hU, hUt⟩` from `hnear.2`. Conclude with `⟨U, hU, fun g hg _ => hUt g hg⟩`.
-/
theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs
  have hnear := GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  refine ⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1,
    GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
