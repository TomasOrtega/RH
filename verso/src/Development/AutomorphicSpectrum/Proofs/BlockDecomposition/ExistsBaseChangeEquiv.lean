import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

/- English proof (translation)
Establish `h` using `GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a`. Use `⟨h.equiv, fun r m => ?_⟩` and prove the remaining obligations. Rewrite using `[h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]`. Both sides reduce to the same expression.
-/
theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
