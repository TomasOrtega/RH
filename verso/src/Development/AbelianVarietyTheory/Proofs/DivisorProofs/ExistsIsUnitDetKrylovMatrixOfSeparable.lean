import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det :=
  @exists_isUnit_det_krylov_of_separable

end GlobalTheory.LeviDesc.Krylov
