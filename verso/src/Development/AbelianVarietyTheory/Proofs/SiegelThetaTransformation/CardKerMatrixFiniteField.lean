import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

/- English proof (translation)
Establish `e : {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} ≃ {H : Submodule F K // Module.finrank F H = 1}` using `{ toFun := fun l => ⟨l.1.comap K.subtype, by`. Rewrite using `[← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr l.2.2]`. Conclude with `l.2.1⟩`. Use `invFun := fun H => ⟨H.1.map K.subtype, by rw [Submodule.finrank_map_subtype_eq]; exact H.2, Submodule.map_subtype_le K H.1⟩`. Use `left_inv := fun l => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.mpr l.2.2`. Use `right_inv := fun H => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `Submodule.comap_map_eq_of_injective K.injective_subtype H.1 }`. Rewrite using `[Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F K)]`. Conclude with `(Projectivization.card' F K).symm`.
-/
theorem card_lines_le_submodule (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} * (Nat.card F - 1) + 1
      = Nat.card K := by
  classical
  have e : {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K}
      ≃ {H : Submodule F K // Module.finrank F H = 1} :=
    { toFun := fun l => ⟨l.1.comap K.subtype, by
        rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
          inf_eq_right.mpr l.2.2]
        exact l.2.1⟩
      invFun := fun H => ⟨H.1.map K.subtype,
        by rw [Submodule.finrank_map_subtype_eq]; exact H.2,
        Submodule.map_subtype_le K H.1⟩
      left_inv := fun l => by
        apply Subtype.ext
        simp only [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr l.2.2
      right_inv := fun H => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective K.injective_subtype H.1 }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F K)]
  exact (Projectivization.card' F K).symm

end GlobalTheory.SW
