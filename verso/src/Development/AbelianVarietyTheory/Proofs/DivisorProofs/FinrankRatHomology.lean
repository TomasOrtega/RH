import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.RatHomology

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_rat_tensor (M : Type) [AddCommGroup M] [Module ℤ M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℤ M := by
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) le_rfl,
    ← IsFractionRing.finrank_right_eq ℤ ℚ]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finrank_rat_homology (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (_ : Module.Finite ℤ (C.homology n)) :
    Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv ℚ C n
  have h := e.finrank_eq
  have hφ : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
  rw [hφ] at h
  rw [h]
  exact finrank_rat_tensor (C.homology n)

end GlobalTheory.RatHomology
