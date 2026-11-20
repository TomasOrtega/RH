import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)`. Rewrite `hg` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Use `⟨(om g : K), ?_⟩` and prove the remaining obligations. Rewrite using `[IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
