import Mathlib

open NumberField Module

namespace Bl.general_b_fact_left_rest

/- English proof (translation)
Use `show Nat.card (G ⧸ N) = Nat.card T`. Use `Nat.card_congr (Equiv.ofBijective (Quotient.lift f ?_) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `a b h`. Conclude with `(hf a b).2 (QuotientGroup.leftRel_apply.mp h)`. Introduce `x y h`.

Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective y`. Conclude with `QuotientGroup.eq.mpr ((hf a b).1 h)`. Introduce `t`. Take `⟨a, rfl⟩` from `hs t`.

Conclude with `⟨(a : G ⧸ N), rfl⟩`.
-/
theorem goal1 {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  show Nat.card (G ⧸ N) = Nat.card T
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift f ?_) ⟨?_, ?_⟩)
  · intro a b h
    exact (hf a b).2 (QuotientGroup.leftRel_apply.mp h)
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr ((hf a b).1 h)
  · intro t
    obtain ⟨a, rfl⟩ := hs t
    exact ⟨(a : G ⧸ N), rfl⟩

end Bl.general_b_fact_left_rest
