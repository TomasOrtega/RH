import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.Cartier.CartierDiv

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
