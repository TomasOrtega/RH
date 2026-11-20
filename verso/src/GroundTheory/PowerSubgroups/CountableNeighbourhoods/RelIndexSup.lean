import Mathlib

namespace GroundTheory.Variant₂.N1

open Subgroup

/- English proof (translation)
Use `symm`. Set `f : N →* (H ⊔ N : Subgroup G)` to `Subgroup.inclusion le_sup_right`. Set `g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)` to `fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by`. Introduce `a b hab`. Rewrite `hab` using `[QuotientGroup.leftRel_apply, mem_subgroupOf]`.

Rewrite using `[QuotientGroup.eq, mem_subgroupOf]`. Simplify `hab)` using `[f]`. Establish `hinj : Function.Injective g`. Introduce `x y hxy`. Proceed by induction on `x using QuotientGroup.induction_on with`.

Consider the case `H a`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H b`. Establish `h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))` using `hxy`. Rewrite `h1` using `[QuotientGroup.eq, mem_subgroupOf]`.

Rewrite using `[QuotientGroup.eq, mem_subgroupOf]`. Simplify `h1` using `[f]`. Establish `hsurj : Function.Surjective g`. Introduce `x`. Proceed by induction on `x using QuotientGroup.induction_on with`.

Consider the case `H k`. Take `⟨y, hy⟩` from `k`. Establish `hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G)`. Rewrite using `[sup_comm]`. Conclude with `hy`.

Rewrite `hy'` using `[coe_mul_of_right_le_normalizer_left N H hLE]`. Take `⟨n, hn, h, hh, rfl⟩` from `hy'`. Use `⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _`. Rewrite using `[QuotientGroup.eq, mem_subgroupOf]`.

Simplify `hh` using `[f]`. Rewrite using `[Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]`. Conclude with `Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)`.
-/
theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end GroundTheory.Variant₂.N1
