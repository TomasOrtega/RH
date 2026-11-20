import Mathlib

namespace GlobalTheory

open Algebra in

/- English proof (translation)
Use `set T := adjoin ℂ ((S : Set L) ∪ (B : Set L)) with hT`. Establish `hBT : ∀ b ∈ B, b ∈ T` using `fun b hb => subset_adjoin (Or.inr hb)`. Set `f : B →+* T` to `{ toFun := fun b => ⟨b.1, hBT b.1 b.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Set `_ : Algebra B T` to `f.toAlgebra`. Establish `: IsScalarTower B T L` using `.of_algebraMap_eq fun _ => rfl`.

Establish `hinj : Function.Injective (algebraMap B T)`. Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val h` as an intermediate fact. Conclude with `this`.

Establish `hzT : IsAlgebraic T z` using `hz.extendScalars hinj`. Establish `hSle : S ≤ adjoin ℂ (S : Set L)` using `subset_adjoin`. Establish `key : IsAlgebraic (adjoin ℂ (S : Set L)) z`. Use `IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℂ) (s := (S : Set L) ∪ (B : Set L)) ?_ hzT` and prove the remaining obligations. Introduce `x hx`.

Break down `hx.1 with h | h` into its components or cases. Conclude with `absurd h hx.2`. Conclude with `(hB x h).tower_top_of_subalgebra_le hSle`. Rewrite `key` using `[Algebra.adjoin_eq]`. Then use the resulting hypothesis.
-/
theorem isAlgebraic_of_subring_isAlgebraic {L : Type} [Field L] [Algebra ℂ L]
    (S : Subalgebra ℂ L) (B : Subring L) (z : L)
    (hB : ∀ b ∈ B, IsAlgebraic S b) (hz : IsAlgebraic B z) : IsAlgebraic S z := by
  set T := adjoin ℂ ((S : Set L) ∪ (B : Set L)) with hT
  have hBT : ∀ b ∈ B, b ∈ T := fun b hb => subset_adjoin (Or.inr hb)
  let f : B →+* T :=
    { toFun := fun b => ⟨b.1, hBT b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra B T := f.toAlgebra
  have : IsScalarTower B T L := .of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap B T) := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hzT : IsAlgebraic T z := hz.extendScalars hinj
  have hSle : S ≤ adjoin ℂ (S : Set L) := subset_adjoin
  have key : IsAlgebraic (adjoin ℂ (S : Set L)) z := by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℂ) (s := (S : Set L) ∪ (B : Set L)) ?_ hzT
    intro x hx
    rcases hx.1 with h | h
    · exact absurd h hx.2
    · exact (hB x h).tower_top_of_subalgebra_le hSle
  rwa [Algebra.adjoin_eq] at key

end GlobalTheory
