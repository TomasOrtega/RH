import Mathlib
import Formalism.HermitianLattices.DefsCS

namespace Formalism.HermitianLatticesTheory

/- English proof (translation)
Introduce `W _ P Q hPQ hfin`. Set `f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q)` to `fun M => (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))`. Use `haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) := Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q)) (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q))) SetLike.coe_injective`. Use `Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce `M hM N hN hMN`.

Establish `key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q → (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q`. Introduce `M hPM _`. Simplify using `only [f]`. Rewrite using `[AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']`. Conclude with `sup_eq_left.mpr fun x hx => AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))`.

Establish `h1 : M.addSubgroupOf Q = N.addSubgroupOf Q`. Rewrite using `[← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]`. Establish `h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M`. Introduce `M hMQ`. Rewrite using `[AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]`.

Rewrite using `[← h2 M hM.2, ← h2 N hN.2, h1]`.
-/
theorem finIntermediate : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]

end Formalism.HermitianLatticesTheory
