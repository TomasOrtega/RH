import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB`. Take `⟨hidx, -, hsum⟩` from `_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a) (fun t _ => (hA t).trans (forall₂_congr fun a _ => ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB`. Use `⟨hidx, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex` using `⟨hAB⟩`. Establish `hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex`.

Use `⟨?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0`. Rewrite using `[hidx]`. Conclude with `hAB`. Use `letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)`.

Use `letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)`. Unfold `_root_.GlobalTheory.FinWeil.sumOp`. Rewrite `hsum`, the goal using `[finsum_eq_sum_of_fintype, map_sum]`. Establish `hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v`. Introduce `a ha b`.

Rewrite using `[hW.comm, hv a ha]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`.

Conclude with `Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _`. Use `_ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[hsum _ (Quotient.out p).2]`. Establish `hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0` using `by conv_rhs => rw [← QuotientAddGroup.out_eq' p]`.

Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Distinguish the cases in `hp : p = 0`. Rewrite using `[if_pos (hmem.2 hp), if_pos hp, hv _ (hmem.2 hp)]`. Conclude with `congrArg (fun n : ℕ => (n : ℂ) • v) hidx`. Rewrite using `[if_neg (mt hmem.1 hp), if_neg hp, zero_smul]`.

Use `_ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B →
    _root_.GlobalTheory.FinWeil.idx A B ≠ 0 →
    _root_.GlobalTheory.FinWeil.idx B A = _root_.GlobalTheory.FinWeil.idx A B ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.sumOp W B A (_root_.GlobalTheory.FinWeil.sumOp W A B v) =
          (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB
  obtain ⟨hidx, -, hsum⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a)
    (fun t _ => (hA t).trans (forall₂_congr fun a _ =>
      ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB
  refine ⟨hidx, fun v hv => ?_⟩
  have hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex := ⟨hAB⟩
  have hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0
    rw [hidx]; exact hAB
  letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  unfold _root_.GlobalTheory.FinWeil.sumOp
  simp_rw [finsum_eq_sum_of_fintype, map_sum] at hsum ⊢
  have hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v := by
    intro a ha b
    rw [hW.comm, hv a ha]
  calc ∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
        ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          W (Quotient.out q).1 (W (Quotient.out p).1 v)
      = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          (∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
            γ (Quotient.out q).1 (Quotient.out p).1) • W (Quotient.out p).1 v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _
    _ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hsum _ (Quotient.out p).2]
        have hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0 := by
          conv_rhs => rw [← QuotientAddGroup.out_eq' p]
          rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        by_cases hp : p = 0
        · rw [if_pos (hmem.2 hp), if_pos hp, hv _ (hmem.2 hp)]
          exact congrArg (fun n : ℕ => (n : ℂ) • v) hidx
        · rw [if_neg (mt hmem.1 hp), if_neg hp, zero_smul]
    _ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
        rw [Finset.sum_ite_eq']
        simp

end GlobalTheory.FinWeil
