import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ V _ _ h N g hspan hN`. Use `haveI : Module.Finite C V := ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range g)⟩`. Establish `h1 : Module.finrank C (⋀[C]^N V) = 1`. Rewrite using `[exteriorPower.finrank_eq, hN, Nat.choose_self]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `htop` using `exteriorPower.ιMulti_span_of_span C N V hspan`. Establish `hle : Submodule.span C (exteriorPower.ιMulti C N '' {a | Set.range a ⊆ Set.range g}) ≤ ⊥`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `- ⟨a, ha, rfl⟩`. Establish `hmem : ∀ i, ∃ j, g j = a i` using `fun i => ha ⟨i, rfl⟩`. Use `choose s hs using hmem`. Establish `: a = g ∘ s` using `funext fun i => (hs i).symm`. Rewrite using `[this, hcon s]`.

Simplify using the standard rewrite rules. Rewrite `hle` using `[htop, le_bot_iff]`. Establish `: Subsingleton (⋀[C]^N V)` using `subsingleton_of_forall_eq 0 fun x => by`. Establish `hx : x ∈ (⊤ : Submodule C (⋀[C]^N V))` using `trivial`. Rewrite `hx` using `[hle]`.

Simplify using `using hx`. Rewrite `h1` using `[Module.finrank_zero_of_subsingleton]`. Conclude with `absurd h1 (by norm_num)`.
-/
theorem topWedge_line_and_nonzero : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  intro C _ V _ _ h N g hspan hN
  haveI : Module.Finite C V := ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range g)⟩
  have h1 : Module.finrank C (⋀[C]^N V) = 1 := by
    rw [exteriorPower.finrank_eq, hN, Nat.choose_self]
  refine ⟨h1, ?_⟩
  by_contra hcon
  push_neg at hcon
  have htop := exteriorPower.ιMulti_span_of_span C N V hspan
  have hle : Submodule.span C (exteriorPower.ιMulti C N '' {a | Set.range a ⊆ Set.range g}) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro - ⟨a, ha, rfl⟩
    have hmem : ∀ i, ∃ j, g j = a i := fun i => ha ⟨i, rfl⟩
    choose s hs using hmem
    have : a = g ∘ s := funext fun i => (hs i).symm
    rw [this, hcon s]
    simp
  rw [htop, le_bot_iff] at hle
  have : Subsingleton (⋀[C]^N V) := subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊤ : Submodule C (⋀[C]^N V)) := trivial
    rw [hle] at hx
    simpa using hx
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory
