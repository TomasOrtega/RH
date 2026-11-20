import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.Cartier.CartierDiv

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[mem_sections, Submodule.mem_one]`. Simplify using `only [regularAt_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨a, ha⟩` from `exists_fnOf_eq (X := X) (U := ⊤) trivial fun x _ => h x`. Conclude with `⟨a, by rw [algebraMap_top]; exact ha⟩`. Introduce and unpack `⟨a, rfl⟩ x`. Rewrite using `[algebraMap_top]`. Conclude with `regAt_fnOf (U := ⊤) trivial trivial a`.
-/
theorem sections_zero_eq_one (X : Scheme.{0}) [IsIntegral X] :
    (0 : CartierDiv X).sections = 1 := by
  ext f
  rw [mem_sections, Submodule.mem_one]
  simp only [regularAt_zero_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_fnOf_eq (X := X) (U := ⊤) trivial fun x _ => h x
    exact ⟨a, by rw [algebraMap_top]; exact ha⟩
  · rintro ⟨a, rfl⟩ x
    rw [algebraMap_top]
    exact regAt_fnOf (U := ⊤) trivial trivial a

end GlobalTheory.Cartier.CartierDiv
