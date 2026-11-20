import Mathlib

namespace GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

def stab {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

/- English proof (translation)
Unfold `stab`. Rewrite using `[Subgroup.mem_inf, Subgroup.mem_map]`. Use `and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify `hk` using `[mul_assoc]`.
-/
theorem mem_stab {G : Type} [Group G] (Γ K : Subgroup G) (y γ : G) :
    γ ∈ stab Γ K y ↔ γ ∈ Γ ∧ y⁻¹ * γ * y ∈ K := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

def DoubleCosetCount : Prop :=
  ∀ (G : Type) [Group G] (Γ U K : Subgroup G), U ≤ K →
    (U.subgroupOf K).FiniteIndex →
    ∀ [Fintype (DoubleCoset.Quotient (Γ : Set G) (K : Set G))],
    (∀ y : G, Finite (stab Γ K y)) →
    (∀ x : G, stab Γ U x = ⊥) →
    ∀ rep : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → G,
      (∀ c, DoubleCoset.mk Γ K (rep c) = c) →
      Finite (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) ∧
      (Nat.card (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) : ℚ) =
        (U.relIndex K : ℚ) *
          ∑ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
            1 / (Nat.card (stab Γ K (rep c)) : ℚ)

/- English proof (translation)
Simplify using `[stab]`.
-/
example {G : Type} [Group G] (Γ : Subgroup G) (x : G) : stab Γ ⊥ x = ⊥ := by
  simp [stab]

/- English proof (translation)
Use extensionality with `γ`. Simplify using `[mem_stab]`.
-/
example {G : Type} [Group G] (Γ : Subgroup G) (x : G) : stab Γ ⊤ x = Γ := by
  ext γ; simp [mem_stab]

/- English proof (translation)
The claim follows from `DoubleCoset.out_eq' Γ K`.
-/
example {G : Type} [Group G] (Γ K : Subgroup G) :
    ∀ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G), DoubleCoset.mk Γ K c.out = c :=
  DoubleCoset.out_eq' Γ K

end GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality
