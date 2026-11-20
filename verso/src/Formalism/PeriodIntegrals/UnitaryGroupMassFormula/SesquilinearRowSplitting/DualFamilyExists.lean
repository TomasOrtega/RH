import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep

open NumberField Module

namespace PI.SRW

/- English proof (translation)
Introduce `E V _ _ _ n g hg`. Set `b` to `Basis.span hg`. Use `choose c hc using fun i => LinearMap.exists_extend (b.coord i)`. Use `⟨c, fun i j => ?_⟩` and prove the remaining obligations. Establish `hmem : g j ∈ Submodule.span E (Set.range g)` using `Submodule.subset_span ⟨j, rfl⟩`.

Establish `h1 : c i (g j) = b.coord i ⟨g j, hmem⟩`. Rewrite using `[← hc i]`. Both sides reduce to the same expression. Establish `h2 : (⟨g j, hmem⟩ : Submodule.span E (Set.range g)) = b j`. Rewrite using `[Basis.span_apply]`.

Rewrite using `[h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem dualFamilyExists : CoordStep := by
  intro E V _ _ _ n g hg
  classical
  let b := Basis.span hg
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨c, fun i j => ?_⟩
  have hmem : g j ∈ Submodule.span E (Set.range g) := Submodule.subset_span ⟨j, rfl⟩
  have h1 : c i (g j) = b.coord i ⟨g j, hmem⟩ := by
    rw [← hc i]; rfl
  have h2 : (⟨g j, hmem⟩ : Submodule.span E (Set.range g)) = b j := by
    rw [Basis.span_apply]
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end PI.SRW
