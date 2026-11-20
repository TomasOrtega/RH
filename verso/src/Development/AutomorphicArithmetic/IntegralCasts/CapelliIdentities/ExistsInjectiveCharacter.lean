import Mathlib

/- English proof (translation)
Introduce `p inst`. Use `haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨Nat.card_pos.ne'⟩`. Establish `hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ)` using `(HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (Nat.card (ZMod p)ˣ)).symm`. Set `e : (ZMod p)ˣ ≃* rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ` to `mulEquivOfCyclicCardEq hcard`. Conclude with `⟨(rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ).subtype.comp e.toMonoidHom, (Subgroup.subtype_injective _).comp e.injective⟩`.
-/
theorem UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char :
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
    ∃ (lam0 : (ZMod p)ˣ →* ℂˣ), Function.Injective (⇑lam0 : (ZMod p)ˣ → ℂˣ) := by
  intro p inst
  haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨Nat.card_pos.ne'⟩
  have hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ) :=
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (Nat.card (ZMod p)ˣ)).symm
  let e : (ZMod p)ˣ ≃* rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ := mulEquivOfCyclicCardEq hcard
  exact ⟨(rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective⟩
