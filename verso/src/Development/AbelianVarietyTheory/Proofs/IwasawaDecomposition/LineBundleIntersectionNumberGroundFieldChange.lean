import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

namespace GroundFieldChange

/- English proof (translation)
The claim follows from `(mul_finsum f c).symm`.
-/
theorem finsum_const_mul_int (c : ℤ) (f : ℕ → ℤ) : ∑ᶠ n, c * f n = c * ∑ᶠ n, f n :=
  (mul_finsum f c).symm

/- English proof (translation)
Rewrite using `[hdim_def, hdim_def, Module.finrank_mul_finrank]`.
-/
theorem hdim_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules)
    (n : ℕ) : hdim κ F n = Module.finrank κ κ' * hdim κ' F n := by
  rw [hdim_def, hdim_def, Module.finrank_mul_finrank]

/- English proof (translation)
Rewrite using `[chi_def, chi_def, ← finsum_const_mul_int]`. Use `finsum_congr fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[hdim_fieldChange κ κ' Z F n, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules) :
    chi κ F = (Module.finrank κ κ' : ℤ) * chi κ' F := by
  rw [chi_def, chi_def, ← finsum_const_mul_int]
  refine finsum_congr fun n ↦ ?_
  rw [hdim_fieldChange κ κ' Z F n, Nat.cast_mul]
  ring

/- English proof (translation)
Introduce `κ κ' _ _ _ Z _ _ _ G ι _ L`. Rewrite using `[interNum_def, interNum_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun S _ ↦ ?_` and prove the remaining obligations. Rewrite using `[chi_fieldChange κ κ' Z]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interNum_fieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules)
    {ι : Type} [Fintype ι] (L : ι → LB Z),
    interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  intro κ κ' _ _ _ Z _ _ _ G ι _ L
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [chi_fieldChange κ κ' Z]
  ring

end GroundFieldChange

end GlobalTheory
