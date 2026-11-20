import Mathlib

namespace GlobalTheory.OneTensorExistence

open TensorProduct

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩`. Consider the case `tmul k l`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective k`. Use `⟨a • l, ?_⟩` and prove the remaining obligations.

Rewrite using `[← TensorProduct.smul_tmul, ← IsLocalRing.ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one]`. Consider the case `add x y hx hy`. Take `⟨u, rfl⟩` from `hx`. Take `⟨v, rfl⟩` from `hy`. Conclude with `⟨u + v, TensorProduct.tmul_add _ _ _⟩`.
-/
theorem exists_one_tmul_eq (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] (z : TensorProduct A (IsLocalRing.ResidueField A) Λ) :
    ∃ y : Λ, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul k l =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    refine ⟨a • l, ?_⟩
    rw [← TensorProduct.smul_tmul, ← IsLocalRing.ResidueField.algebraMap_eq,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, TensorProduct.tmul_add _ _ _⟩

end GlobalTheory.OneTensorExistence
