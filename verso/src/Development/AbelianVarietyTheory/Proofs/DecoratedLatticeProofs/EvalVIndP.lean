import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField

namespace GlobalTheory.VacLoc

variable {D : D7}

open scoped Classical

def indP (D : D7) (X : Set (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ X then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_indP (X : Set (Pl D)) (v : Pl D) :
    evalV D.host.F v (indP D X) = if v ∈ X then 1 else 0 := rfl

/- English proof (translation)
Apply the tactic sequence `intro v; rw [evalV_indP]; by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]`.
-/
theorem indicatorAdele_mem_integralAdeles (X : Set (Pl D)) : indP D X ∈ intAf D.host.F := by
  intro v; rw [evalV_indP]; by_cases h : v ∈ X <;> simp [h, one_mem, zero_mem]

/- English proof (translation)
The claim follows from `RestrictedProduct.ext _ _ h`.
-/
theorem finiteAdele_ext {a b : Af D.host.F} (h : ∀ v, evalV D.host.F v a = evalV D.host.F v b) : a = b :=
  RestrictedProduct.ext _ _ h

/- English proof (translation)
Apply `finiteAdele_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[map_mul, evalV_indP, evalV_indP, evalV_indP]`. Apply the tactic sequence `by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]`.
-/
theorem indicatorAdele_singleton_mul_singleton (X Y : Set (Pl D)) : indP D X * indP D Y = indP D (X ∩ Y) := by
  apply finiteAdele_ext; intro v; rw [map_mul, evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]

/- English proof (translation)
Apply `finiteAdele_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[map_add, evalV_indP, evalV_indP, evalV_indP]`. Apply the tactic sequence `by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]`. Conclude with `Set.disjoint_left.mp h hX hY`.
-/
theorem indicatorAdele_union_of_disjoint {X Y : Set (Pl D)} (h : Disjoint X Y) : indP D X + indP D Y = indP D (X ∪ Y) := by
  apply finiteAdele_ext; intro v; rw [map_add, evalV_indP, evalV_indP, evalV_indP]
  by_cases hX : v ∈ X <;> by_cases hY : v ∈ Y <;> simp [hX, hY]
  exact Set.disjoint_left.mp h hX hY

/- English proof (translation)
Apply `finiteAdele_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[evalV_indP, map_one]`. Simplify using the standard rewrite rules.
-/
theorem indicatorAdele_univ : indP D Set.univ = 1 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_one]; simp

/- English proof (translation)
Apply `finiteAdele_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[evalV_indP, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem indicatorAdele_empty : indP D ∅ = 0 := by
  apply finiteAdele_ext; intro v; rw [evalV_indP, map_zero]; simp

end GlobalTheory.VacLoc

end
