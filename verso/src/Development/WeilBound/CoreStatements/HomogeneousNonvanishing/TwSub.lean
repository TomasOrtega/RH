import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `O _ s L _ _ f I hI x hx`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha y _`. Establish `hsa : s a ∈ I` using `hI (Ideal.mem_map_of_mem (s : O →+* O) ha)`. Establish `key : (show L from f (a • y)) = s a • (show L from f y)` using `f.map_smul a y`.

Rewrite using `[key]`. Conclude with `Submodule.smul_mem_smul hsa Submodule.mem_top`. Introduce `y z hy hz`. Establish `key : (show L from f (y + z)) = (show L from f y) + (show L from f z)` using `f.map_add y z`. Rewrite using `[key]`.

Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem tw_sub : ∀ (O : Type) [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] (f : L →ₗ[O] TwMod s L) (I : Ideal O), I.map (s : O →+* O) ≤ I → ∀ x ∈ I • (⊤ : Submodule O L), (show L from f x) ∈ I • (⊤ : Submodule O L) := by
  intro O _ s L _ _ f I hI x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have hsa : s a ∈ I := hI (Ideal.mem_map_of_mem (s : O →+* O) ha)
    have key : (show L from f (a • y)) = s a • (show L from f y) := f.map_smul a y
    rw [key]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  · intro y z hy hz
    have key : (show L from f (y + z)) = (show L from f y) + (show L from f z) := f.map_add y z
    rw [key]
    exact Submodule.add_mem _ hy hz

end PositivityTheory.UnitarySelfGeneration
