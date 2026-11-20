import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Establish `hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔ (LinearMap.range ((1 - b) * P)).map a`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x)`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hx]`. Conclude with `Submodule.add_mem_sup (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)) (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))`. Establish `h1` using `Submodule.finrank_mono hle`. Establish `h2` using `Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ((LinearMap.range ((1 - b) * P)).map a)`. Establish `h3` using `Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))`.

Establish `h4` using `Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_range_le_three (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (P a b : Module.End ℂ M) :
    Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - a) * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  have hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔
      (LinearMap.range ((1 - b) * P)).map a := by
    rintro _ ⟨x, rfl⟩
    have hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x) := by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P))
    ((LinearMap.range ((1 - b) * P)).map a)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))
  have h4 := Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))
  omega

end GlobalTheory.BadShare
